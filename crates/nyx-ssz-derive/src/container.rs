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
    let encode = encode_method(&fields, krate);
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

fn encode_method(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let sizing = fields.iter().map(|f| {
        let name = &f.ident;
        quote!(size.push(&self.#name)?;)
    });
    let prepare = fields.iter().enumerate().map(|(i, f)| {
        let name = &f.ident;
        let local = format_ident!("__ssz_size_{}", i);
        quote!(let #local = size.push(&self.#name)?;)
    });
    let writes = fields.iter().enumerate().map(|(i, f)| {
        let name = &f.ident;
        let local = format_ident!("__ssz_size_{}", i);
        quote!(writer.push(&self.#name, #local.ok_or(#krate::error::CodecError::NativeOutputOverflow)?)?;)
    });
    quote! {
        fn encoded_len(&self) -> ::core::result::Result<usize, #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            let mut size = #krate::encoding::ContainerSize::default();
            #(#sizing)*
            size.finish().map(|(_, total)| total)
        }
        fn encode_into(&self, output: &mut [u8]) -> ::core::result::Result<(), #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            let mut size = #krate::encoding::ContainerSize::default();
            #(#prepare)*
            let (leading, total) = size.finish()?;
            #krate::encoding::check_length(output, total)?;
            let mut writer = #krate::encoding::ContainerWriter::new(output, leading)?;
            #(#writes)*
            writer.finish()
        }
    }
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
    let declaration = quote! {
        if let ::core::result::Result::Err(kind) = const { #krate::codec::validate_type::<Self>() } {
            return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state });
        }
    };
    let fixed = if progressive {
        quote!()
    } else {
        fixed_decode(&names, &types, krate)
    };
    quote! {
        fn decode(bytes: &[u8]) -> ::core::result::Result<Self, #krate::error::DecodeFailure<Self::DecodeState>> {
            let mut state = #state_name { #(#names: ::core::default::Default::default(),)* #marker: ::core::marker::PhantomData };
            #declaration
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
    let layout = const_layout(types, krate);
    let reads = names
        .iter()
        .zip(types)
        .enumerate()
        .map(|(index, (name, ty))| fixed_split(index, name, ty, krate));
    quote! {
        if bytes.len() as u128 >= 4_294_967_296 {
            return ::core::result::Result::Err(#krate::error::DecodeFailure {
                kind: #krate::error::CodecError::SizeOverflow, state,
            });
        }
        match #layout {
            ::core::result::Result::Ok(::core::option::Option::Some((total, __ssz_widths))) => {
                if bytes.len() != total {
                    return ::core::result::Result::Err(#krate::error::DecodeFailure {
                        kind: #krate::error::CodecError::InvalidLength, state,
                    });
                }
                let mut __ssz_rest = bytes;
                #(#reads)*
                if !__ssz_rest.is_empty() {
                    return ::core::result::Result::Err(#krate::error::DecodeFailure {
                        kind: #krate::error::CodecError::InvalidLength, state,
                    });
                }
                return ::core::result::Result::Ok(Self {
                    #(#names: state.#names.value.take().expect("completed SSZ field"),)*
                });
            }
            ::core::result::Result::Ok(::core::option::Option::None) => {}
            ::core::result::Result::Err(kind) => {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state });
            }
        }
    }
}

fn const_layout(types: &[&syn::Type], krate: &TokenStream) -> TokenStream {
    let calls = types
        .iter()
        .map(|ty| quote!(#krate::codec::fixed_size::<#ty>()));
    quote! {
        const { #krate::codec::fixed_layout([#(#calls,)*]) }
    }
}

fn fixed_split(
    index: usize,
    name: &syn::Ident,
    ty: &syn::Type,
    krate: &TokenStream,
) -> TokenStream {
    quote! {
        let ::core::option::Option::Some((__ssz_slice, __ssz_next)) =
            __ssz_rest.split_at_checked(__ssz_widths[#index]) else {
            return ::core::result::Result::Err(#krate::error::DecodeFailure {
                kind: #krate::error::CodecError::InvalidLength, state,
            });
        };
        __ssz_rest = __ssz_next;
        match <#ty as #krate::codec::Ssz>::decode(__ssz_slice) {
            ::core::result::Result::Ok(value) => state.#name.value = ::core::option::Option::Some(value),
            ::core::result::Result::Err(failure) => {
                state.#name.child = ::core::option::Option::Some(failure.state);
                return ::core::result::Result::Err(#krate::error::DecodeFailure {
                    kind: failure.kind, state,
                });
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
