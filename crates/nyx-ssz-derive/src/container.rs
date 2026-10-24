use crate::container_marker::marker_name;
use crate::{
    attributes::{self, Field},
    bounded_generics, state_name,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{DataStruct, DeriveInput};

pub fn expand(
    input: &DeriveInput,
    data: &DataStruct,
    progressive: bool,
    krate: &TokenStream,
) -> syn::Result<TokenStream> {
    let mut fields = attributes::fields(data, progressive)?;
    fields.sort_by_key(|field| field.position);
    let types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let generics = bounded_generics(input, &types, krate);
    let (params, args, bounds) = generics.split_for_impl();
    let name = &input.ident;
    let state_name = state_name(input);
    let state = state_definition(input, &fields, &generics, krate);
    let (descriptor, mask) = metadata(&fields, progressive, krate);
    let encode = encode_method(&fields, krate, progressive);
    let decode = decode_method(&fields, &state_name, krate, progressive);
    let root = root_method(&fields, &mask, krate);
    Ok(quote! {
        #state
        impl #params #krate::codec::Ssz for #name #args #bounds {
            type DecodeState = #state_name #args;
            const TYPE: &'static #krate::type_info::TypeDescriptor = &#descriptor;
            #encode #decode #root
        }
    })
}

fn state_definition(
    input: &DeriveInput,
    fields: &[Field],
    generics: &syn::Generics,
    krate: &TokenStream,
) -> TokenStream {
    let (params, args, bounds) = generics.split_for_impl();
    let parent = &input.ident;
    let state = state_name(input);
    let marker = marker_name(fields);
    let names = fields.iter().map(|f| &f.ident);
    let types = fields.iter().map(|f| &f.ty);
    quote! {
        pub struct #state #params #bounds {
            #(pub #names: #krate::composite::FieldDecodeState<#types>,)*
            #marker: ::core::marker::PhantomData<fn() -> #parent #args>,
        }
    }
}

fn encode_method(fields: &[Field], krate: &TokenStream, progressive: bool) -> TokenStream {
    if progressive {
        return slow_encode(fields, krate);
    }
    let classify = classify_fixed(fields, krate);
    let writes = write_fixed(fields, krate);
    fast_encode_impl(
        classify.clone(),
        writes.clone(),
        slow_len_body(fields, krate),
        slow_into_body(fields, krate),
        allocating_encode(&classify, &writes, krate),
        krate,
    )
}

fn allocating_encode(
    classify: &TokenStream,
    writes: &TokenStream,
    krate: &TokenStream,
) -> TokenStream {
    quote! {
        fn encode(&self) -> ::core::result::Result<::std::vec::Vec<u8>, #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #classify
            if !__ssz_slow {
                let __ssz_total = #krate::encoding::finish_fixed_total(__ssz_total, __ssz_oversize)?;
                let mut __ssz_output = ::std::vec![0; __ssz_total];
                {
                    let mut __ssz_rest = __ssz_output.as_mut_slice();
                    #writes
                    if !__ssz_rest.is_empty() {
                        return ::core::result::Result::Err(#krate::error::CodecError::InvalidLength);
                    }
                }
                return ::core::result::Result::Ok(__ssz_output);
            }
            let mut __ssz_output = ::std::vec![0; self.encoded_len()?];
            self.encode_into(&mut __ssz_output)?;
            ::core::result::Result::Ok(__ssz_output)
        }
    }
}

fn fast_encode_impl(
    classify: TokenStream,
    writes: TokenStream,
    length: TokenStream,
    write: TokenStream,
    allocating: TokenStream,
    krate: &TokenStream,
) -> TokenStream {
    quote! {
        fn encoded_len(&self) -> ::core::result::Result<usize, #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #classify
            if !__ssz_slow {
                return #krate::encoding::finish_fixed_total(__ssz_total, __ssz_oversize);
            }
            #length
        }
        fn encode_into(&self, output: &mut [u8]) -> ::core::result::Result<(), #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #classify
            if !__ssz_slow {
                let __ssz_total = #krate::encoding::finish_fixed_total(__ssz_total, __ssz_oversize)?;
                #krate::encoding::check_length(output, __ssz_total)?;
                let mut __ssz_rest = output;
                #writes
                return if __ssz_rest.is_empty() {
                    ::core::result::Result::Ok(())
                } else {
                    ::core::result::Result::Err(#krate::error::CodecError::InvalidLength)
                };
            }
            #write
        }
        #allocating
    }
}

fn slow_len_body(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let sizing = fields.iter().map(|field| {
        let name = &field.ident;
        quote!(size.push(&self.#name)?;)
    });
    quote! {
        let mut size = #krate::encoding::ContainerSize::default();
        #(#sizing)*
        size.finish().map(|(_, total)| total)
    }
}

fn slow_into_body(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let prepare = fields.iter().enumerate().map(|(index, field)| {
        let name = &field.ident;
        let local = format_ident!("__ssz_size_{}", index);
        quote!(let #local = size.push(&self.#name)?;)
    });
    let writes = fields.iter().enumerate().map(|(index, field)| {
        let name = &field.ident;
        let local = format_ident!("__ssz_size_{}", index);
        quote!(writer.push(&self.#name, #local.ok_or(#krate::error::CodecError::NativeOutputOverflow)?)?;)
    });
    quote! {
        let mut size = #krate::encoding::ContainerSize::default();
        #(#prepare)*
        let (leading, total) = size.finish()?;
        #krate::encoding::check_length(output, total)?;
        let mut writer = #krate::encoding::ContainerWriter::new(output, leading)?;
        #(#writes)*
        writer.finish()
    }
}

fn slow_encode(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let length = slow_len_body(fields, krate);
    let write = slow_into_body(fields, krate);
    quote! {
        fn encoded_len(&self) -> ::core::result::Result<usize, #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #length
        }
        fn encode_into(&self, output: &mut [u8]) -> ::core::result::Result<(), #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #write
        }
    }
}

fn classify_fixed(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let fields = fields.iter().enumerate().map(|(index, field)| {
        let name = &field.ident;
        let local = format_ident!("__ssz_len_{}", index);
        quote! {
            let #local = match #krate::encoding::fixed_child(&self.#name)? {
                #krate::encoding::FixedChild::Fixed(length) => {
                    __ssz_total = match __ssz_total.checked_add(length as u128) {
                        ::core::option::Option::Some(next) => next,
                        ::core::option::Option::None => {
                            return ::core::result::Result::Err(#krate::error::CodecError::SizeOverflow);
                        }
                    };
                    ::core::option::Option::Some(length)
                }
                #krate::encoding::FixedChild::DeferredOverflow => {
                    __ssz_oversize = true;
                    ::core::option::Option::None
                }
                #krate::encoding::FixedChild::NotFixed => {
                    __ssz_slow = true;
                    ::core::option::Option::None
                }
            };
        }
    });
    quote! {
        let mut __ssz_total = 0_u128;
        let mut __ssz_oversize = false;
        let mut __ssz_slow = false;
        #(#fields)*
    }
}

fn write_fixed(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let writes = fields.iter().enumerate().map(|(index, field)| {
        let name = &field.ident;
        let local = format_ident!("__ssz_len_{}", index);
        quote! {
            let __ssz_width = #local.ok_or(#krate::error::CodecError::InvalidLength)?;
            if __ssz_width > __ssz_rest.len() {
                return ::core::result::Result::Err(#krate::error::CodecError::InvalidLength);
            }
            let (__ssz_slot, __ssz_next) = __ssz_rest.split_at_mut(__ssz_width);
            __ssz_rest = __ssz_next;
            #krate::codec::Ssz::encode_into(&self.#name, __ssz_slot)?;
        }
    });
    quote!(#(#writes)*)
}

fn root_method(fields: &[Field], mask: &TokenStream, krate: &TokenStream) -> TokenStream {
    let roots = fields.iter().map(|f| {
        let n = &f.ident;
        quote!(#krate::codec::Ssz::hash_tree_root(&self.#n)?)
    });
    quote! {
        fn hash_tree_root(&self) -> ::core::result::Result<[u8;32], #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            #krate::composite::root_fields(&[#(#roots,)*], #mask)
        }
    }
}

fn metadata(
    fields: &[Field],
    progressive: bool,
    krate: &TokenStream,
) -> (TokenStream, TokenStream) {
    let names = fields.iter().map(|f| &f.name);
    let types = fields.iter().map(|f| &f.ty);
    if !progressive {
        return (
            quote!(#krate::type_info::TypeDescriptor::Container(&[#(#names,)*], &[#(<#types as #krate::codec::Ssz>::TYPE,)*])),
            quote!(::core::option::Option::None),
        );
    }
    let mut mask = vec![false; fields.last().expect("nonempty fields").position + 1];
    for field in fields {
        mask[field.position] = true;
    }
    (
        quote!(#krate::type_info::TypeDescriptor::ProgressiveContainer(&[#(#mask,)*], &[#(#names,)*], &[#(<#types as #krate::codec::Ssz>::TYPE,)*])),
        quote!(::core::option::Option::Some(&[#(#mask,)*])),
    )
}

fn decode_method(
    fields: &[Field],
    state_name: &syn::Ident,
    krate: &TokenStream,
    progressive: bool,
) -> TokenStream {
    let names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    let marker = marker_name(fields);
    let decode = fields
        .iter()
        .enumerate()
        .map(|(index, field)| decode_field(index, field, krate));
    let fixed = if progressive {
        quote!()
    } else {
        fixed_decode(&names, &types, krate)
    };
    quote! {
        fn decode(bytes: &[u8]) -> ::core::result::Result<Self, #krate::error::DecodeFailure<Self::DecodeState>> {
            let mut state = #state_name { #(#names: ::core::default::Default::default(),)* #marker: ::core::marker::PhantomData };
            if let ::core::result::Result::Err(kind) = #krate::codec::validate_type::<Self>() {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state });
            }
            #fixed
            let view = match #krate::container::container_view(bytes, &[#(#krate::codec::fixed_size::<#types>(),)*]) {
                ::core::result::Result::Ok(view) => view,
                ::core::result::Result::Err(kind) => return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state }),
            };
            #(#decode)*
            ::core::result::Result::Ok(Self { #(#names: state.#names.value.take().expect("completed SSZ field"),)* })
        }
    }
}

fn fixed_decode(names: &[&syn::Ident], types: &[&syn::Type], krate: &TokenStream) -> TokenStream {
    let reads = names
        .iter()
        .zip(types)
        .map(|(name, ty)| fixed_field(name, ty, krate));
    quote! {
        match #krate::container::fixed_container_cursor(bytes, &[#(#krate::codec::fixed_size::<#types>(),)*]) {
            ::core::result::Result::Ok(::core::option::Option::Some(mut cursor)) => {
                #(#reads)*
                return ::core::result::Result::Ok(Self { #(#names: state.#names.value.take().expect("completed SSZ field"),)* });
            }
            ::core::result::Result::Ok(::core::option::Option::None) => {}
            ::core::result::Result::Err(kind) => {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state });
            }
        }
    }
}

fn fixed_field(name: &syn::Ident, ty: &syn::Type, krate: &TokenStream) -> TokenStream {
    quote! {
        let slice = match cursor.read(match #krate::codec::fixed_size::<#ty>() {
            ::core::result::Result::Ok(::core::option::Option::Some(width)) => width,
            _ => return ::core::result::Result::Err(#krate::error::DecodeFailure {
                kind: #krate::error::CodecError::InvalidLength,
                state,
            }),
        }) {
            ::core::result::Result::Ok(slice) => slice,
            ::core::result::Result::Err(kind) => {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state });
            }
        };
        match <#ty as #krate::codec::Ssz>::decode(slice) {
            ::core::result::Result::Ok(value) => state.#name.value = ::core::option::Option::Some(value),
            ::core::result::Result::Err(failure) => {
                state.#name.child = ::core::option::Option::Some(failure.state);
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind: failure.kind, state });
            }
        }
    }
}

fn decode_field(index: usize, field: &Field, krate: &TokenStream) -> TokenStream {
    let name = &field.ident;
    let ty = &field.ty;
    quote! {
        match <#ty as #krate::codec::Ssz>::decode(view.get(#index).expect("validated SSZ field range")) {
            ::core::result::Result::Ok(value) => state.#name.value = ::core::option::Option::Some(value),
            ::core::result::Result::Err(failure) => {
                state.#name.child = ::core::option::Option::Some(failure.state);
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind: failure.kind, state });
            }
        }
    }
}
