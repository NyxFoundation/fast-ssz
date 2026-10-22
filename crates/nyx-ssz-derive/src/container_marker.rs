use crate::attributes::Field;
use syn::ext::IdentExt;

pub(super) fn marker_name(fields: &[Field]) -> syn::Ident {
    let mut name = quote::format_ident!("__nyx_ssz_marker");
    while fields.iter().any(|field| field.ident.unraw() == name) {
        name = quote::format_ident!("{}_", name);
    }
    name
}
