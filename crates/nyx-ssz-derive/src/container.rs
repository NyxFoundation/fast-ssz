use crate::{
    attributes::{self, Field},
    bounded_generics,
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
    let types: Vec<_> = fields.iter().map(|field| &field.ty).collect();
    let generics = bounded_generics(input, &types, krate);
    let (params, args, bounds) = generics.split_for_impl();
    let name = &input.ident;
    let (descriptor, mask) = metadata(&fields, progressive, krate);
    let encode = encode_method(&fields, krate);
    let decode = decode_method(&fields, krate, progressive);
    let root = root_method(&fields, &mask, krate);
    Ok(quote! {
        impl #params #krate::codec::Ssz for #name #args #bounds {
            const TYPE: &'static #krate::type_info::TypeDescriptor = &#descriptor;
            #encode #decode #root
        }
    })
}

fn encode_method(fields: &[Field], krate: &TokenStream) -> TokenStream {
    let sizing = fields.iter().map(|field| {
        let name = &field.ident;
        quote!(size.push(&self.#name)?;)
    });
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
    let roots = fields.iter().map(|field| {
        let name = &field.ident;
        quote!(#krate::codec::Ssz::hash_tree_root(&self.#name)?)
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
    let names = fields.iter().map(|field| &field.name);
    let types = fields.iter().map(|field| &field.ty);
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

fn decode_method(fields: &[Field], krate: &TokenStream, progressive: bool) -> TokenStream {
    let names: Vec<_> = fields.iter().map(|field| &field.ident).collect();
    let types: Vec<_> = fields.iter().map(|field| &field.ty).collect();
    let fixed = if progressive {
        quote!()
    } else {
        fixed_decode(&names, &types, krate)
    };
    let layout = const_container_layout(&types, krate);
    let values = fields
        .iter()
        .enumerate()
        .map(|(index, field)| decode_field(index, field, krate));
    quote! {
        fn decode(bytes: &[u8]) -> ::core::result::Result<Self, #krate::error::CodecError> {
            const { #krate::codec::validate_type::<Self>() }?;
            #fixed
            let __ssz_ranges = #krate::container::derived_container_ranges(bytes, #layout)?;
            ::core::result::Result::Ok(Self { #(#values,)* })
        }
    }
}

fn fixed_decode(names: &[&syn::Ident], types: &[&syn::Type], krate: &TokenStream) -> TokenStream {
    let layout = const_fixed_layout(types, krate);
    let locals: Vec<_> = (0..names.len())
        .map(|index| format_ident!("__ssz_field_{}", index))
        .collect();
    let reads = locals
        .iter()
        .zip(types)
        .enumerate()
        .map(|(index, (local, ty))| fixed_split(index, local, ty, krate));
    quote! {
        if bytes.len() as u128 >= 4_294_967_296 {
            return ::core::result::Result::Err(#krate::error::CodecError::SizeOverflow);
        }
        match #layout {
            ::core::result::Result::Ok(::core::option::Option::Some((total, __ssz_widths))) => {
                if bytes.len() != total {
                    return ::core::result::Result::Err(#krate::error::CodecError::InvalidLength);
                }
                let mut __ssz_rest = bytes;
                #(#reads)*
                return ::core::result::Result::Ok(Self {
                    #(#names: #locals,)*
                });
            }
            ::core::result::Result::Ok(::core::option::Option::None) => {}
            ::core::result::Result::Err(kind) => return ::core::result::Result::Err(kind),
        }
    }
}

fn const_fixed_layout(types: &[&syn::Type], krate: &TokenStream) -> TokenStream {
    let calls = types
        .iter()
        .map(|ty| quote!(#krate::codec::fixed_size::<#ty>()));
    quote! {
        const { #krate::codec::fixed_layout([#(#calls,)*]) }
    }
}

fn const_container_layout(types: &[&syn::Type], krate: &TokenStream) -> TokenStream {
    let calls = types
        .iter()
        .map(|ty| quote!(#krate::codec::fixed_size::<#ty>()));
    quote! {
        const { #krate::container::derived_container_layout([#(#calls,)*]) }
    }
}

fn fixed_split(
    index: usize,
    local: &syn::Ident,
    ty: &syn::Type,
    krate: &TokenStream,
) -> TokenStream {
    quote! {
        let ::core::option::Option::Some((__ssz_slice, __ssz_next)) =
            __ssz_rest.split_at_checked(__ssz_widths[#index]) else {
            return ::core::result::Result::Err(#krate::error::CodecError::InvalidLength);
        };
        __ssz_rest = __ssz_next;
        let #local = <#ty as #krate::codec::Ssz>::decode(__ssz_slice)?;
    }
}

fn decode_field(index: usize, field: &Field, krate: &TokenStream) -> TokenStream {
    let name = &field.ident;
    let ty = &field.ty;
    quote! {
        #name: {
            let __ssz_range = __ssz_ranges[#index];
            <#ty as #krate::codec::Ssz>::decode(&bytes[__ssz_range.start..__ssz_range.end])?
        }
    }
}
