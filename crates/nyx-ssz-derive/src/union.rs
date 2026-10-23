use crate::{attributes, bounded_generics, state_name};
use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashSet;
use syn::{DataEnum, DeriveInput, Error, Ident, Type};

struct Variant {
    name: Ident,
    ty: Type,
    selector: usize,
}

fn variants(data: &DataEnum) -> syn::Result<Vec<Variant>> {
    if data.variants.is_empty() {
        return Err(Error::new_spanned(
            data.enum_token,
            "SSZ union cannot be empty",
        ));
    }
    let mut seen = HashSet::new();
    data.variants
        .iter()
        .map(|value| parse_variant(value, &mut seen))
        .collect()
}

fn parse_variant(variant: &syn::Variant, seen: &mut HashSet<usize>) -> syn::Result<Variant> {
    let attrs = attributes::parse(&variant.attrs)?;
    if attrs.progressive
        || attrs.position.is_some()
        || attrs.rename.is_some()
        || variant.discriminant.is_some()
    {
        return Err(Error::new_spanned(
            variant,
            "union variants use only selector attributes",
        ));
    }
    let selector = attrs
        .selector
        .ok_or_else(|| Error::new_spanned(variant, "union variant requires selector"))?;
    if !(1..=127).contains(&selector) || !seen.insert(selector) {
        return Err(Error::new_spanned(
            variant,
            "selectors must be distinct and in 1..=127",
        ));
    }
    let syn::Fields::Unnamed(fields) = &variant.fields else {
        return Err(Error::new_spanned(
            variant,
            "union variant requires one unnamed payload",
        ));
    };
    if fields.unnamed.len() != 1
        || fields.unnamed[0]
            .attrs
            .iter()
            .any(|attr| attr.path().is_ident("ssz"))
    {
        return Err(Error::new_spanned(
            fields,
            "union variant requires one payload without SSZ field attributes",
        ));
    }
    Ok(Variant {
        name: variant.ident.clone(),
        ty: fields.unnamed[0].ty.clone(),
        selector,
    })
}

pub fn expand(
    input: &DeriveInput,
    data: &DataEnum,
    krate: &TokenStream,
) -> syn::Result<TokenStream> {
    let variants = variants(data)?;
    let names: Vec<_> = variants.iter().map(|v| &v.name).collect();
    let types: Vec<_> = variants.iter().map(|v| &v.ty).collect();
    let selectors = variants.iter().map(|v| v.selector);
    let generics = bounded_generics(input, &types, krate);
    let (params, args, bounds) = generics.split_for_impl();
    let name = &input.ident;
    let state = state_name(input);
    let encode = encode_method(&variants, krate);
    let decode = decode_method(&variants, &state, krate);
    let root = root_method(&variants, krate);
    Ok(quote! {
        pub enum #state #params #bounds { #(#names(<#types as #krate::codec::Ssz>::DecodeState),)* }
        impl #params #krate::codec::Ssz for #name #args #bounds {
            type DecodeState = ::core::option::Option<#state #args>;
            const TYPE: &'static #krate::type_info::TypeDescriptor = &#krate::type_info::TypeDescriptor::CompatibleUnion(&[#(#selectors,)*], &[#(<#types as #krate::codec::Ssz>::TYPE,)*]);
            #encode #decode #root
        }
    })
}

fn encode_method(variants: &[Variant], krate: &TokenStream) -> TokenStream {
    let sizes = variants.iter().map(|v| {
        let name = &v.name;
        quote!(Self::#name(value) => #krate::encoding::union_len(value),)
    });
    let writes = variants.iter().map(|v| {
        let name = &v.name;
        let tag = v.selector as u8;
        quote!(Self::#name(value) => {
            output[0] = #tag;
            #krate::codec::Ssz::encode_into(value, &mut output[1..])
        },)
    });
    quote! {
        fn encoded_len(&self) -> ::core::result::Result<usize, #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            match self { #(#sizes)* }
        }
        fn encode_into(&self, output: &mut [u8]) -> ::core::result::Result<(), #krate::error::CodecError> {
            #krate::encoding::check_length(output, #krate::codec::Ssz::encoded_len(self)?)?;
            match self { #(#writes)* }
        }
    }
}

fn root_method(variants: &[Variant], krate: &TokenStream) -> TokenStream {
    let arms = variants.iter().map(|v| {
        let name = &v.name;
        let tag = v.selector as u8;
        quote!(Self::#name(value) => #krate::composite::root_union(#tag, value),)
    });
    quote! {
        fn hash_tree_root(&self) -> ::core::result::Result<[u8;32], #krate::error::CodecError> {
            #krate::codec::validate_type::<Self>()?;
            match self { #(#arms)* }
        }
    }
}

fn decode_method(variants: &[Variant], state: &Ident, krate: &TokenStream) -> TokenStream {
    let arms = variants.iter().map(|v| {
        let name=&v.name; let ty=&v.ty; let tag=v.selector as u8;
        quote!(#tag => <#ty as #krate::codec::Ssz>::decode(body).map(Self::#name).map_err(|failure| #krate::error::DecodeFailure { kind: failure.kind, state: ::core::option::Option::Some(#state::#name(failure.state)) }),)
    });
    quote! {
        fn decode(bytes: &[u8]) -> ::core::result::Result<Self, #krate::error::DecodeFailure<Self::DecodeState>> {
            if let ::core::result::Result::Err(kind) = #krate::codec::validate_type::<Self>() {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind, state: ::core::option::Option::None });
            }
            let ::core::option::Option::Some((&selector, body)) = bytes.split_first() else {
                return ::core::result::Result::Err(#krate::error::DecodeFailure { kind: #krate::error::CodecError::NoSelector, state: ::core::option::Option::None });
            };
            match selector {
                #(#arms)*
                _ => ::core::result::Result::Err(#krate::error::DecodeFailure { kind: #krate::error::CodecError::UnknownSelector, state: ::core::option::Option::None }),
            }
        }
    }
}
