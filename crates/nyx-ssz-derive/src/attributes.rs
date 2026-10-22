use std::collections::HashSet;
use syn::{Attribute, Error, Ident, LitInt, LitStr, Type};

#[derive(Default)]
pub struct Attributes {
    pub progressive: bool,
    pub position: Option<usize>,
    pub selector: Option<usize>,
    pub rename: Option<String>,
}

pub fn parse(attributes: &[Attribute]) -> syn::Result<Attributes> {
    let mut result = Attributes::default();
    let mut seen = HashSet::new();
    for attribute in attributes.iter().filter(|a| a.path().is_ident("ssz")) {
        attribute.parse_nested_meta(|meta| {
            let name = meta
                .path
                .get_ident()
                .ok_or_else(|| meta.error("expected SSZ attribute"))?
                .to_string();
            if !seen.insert(name.clone()) {
                return Err(meta.error("duplicate SSZ attribute"));
            }
            match name.as_str() {
                "progressive" => result.progressive = true,
                "position" => {
                    result.position = Some(meta.value()?.parse::<LitInt>()?.base10_parse()?)
                }
                "selector" => {
                    result.selector = Some(meta.value()?.parse::<LitInt>()?.base10_parse()?)
                }
                "rename" => result.rename = Some(meta.value()?.parse::<LitStr>()?.value()),
                _ => return Err(meta.error("unknown SSZ attribute")),
            }
            Ok(())
        })?;
    }
    Ok(result)
}

pub struct Field {
    pub ident: Ident,
    pub ty: Type,
    pub name: String,
    pub position: usize,
}

pub fn fields(data: &syn::DataStruct, progressive: bool) -> syn::Result<Vec<Field>> {
    let syn::Fields::Named(fields) = &data.fields else {
        return Err(Error::new_spanned(
            &data.fields,
            "SSZ containers require named fields",
        ));
    };
    if fields.named.is_empty() {
        return Err(Error::new_spanned(fields, "SSZ containers cannot be empty"));
    }
    let mut names = HashSet::new();
    let mut positions = HashSet::new();
    fields
        .named
        .iter()
        .enumerate()
        .map(|(index, field)| {
            let parsed = parse_field(field, index, progressive)?;
            if !positions.insert(parsed.position) || !names.insert(parsed.name.clone()) {
                return Err(Error::new_spanned(
                    field,
                    "duplicate SSZ position or field name",
                ));
            }
            Ok(parsed)
        })
        .collect()
}

fn parse_field(field: &syn::Field, index: usize, progressive: bool) -> syn::Result<Field> {
    let attrs = parse(&field.attrs)?;
    if attrs.progressive || attrs.selector.is_some() || (!progressive && attrs.position.is_some()) {
        return Err(Error::new_spanned(
            field,
            "invalid container field attribute",
        ));
    }
    let ident = field.ident.clone().expect("named field");
    let raw = ident.to_string();
    let name = attrs
        .rename
        .unwrap_or_else(|| raw.strip_prefix("r#").unwrap_or(&raw).to_owned());
    let position = if progressive {
        attrs
            .position
            .ok_or_else(|| Error::new_spanned(field, "progressive fields require position"))?
    } else {
        index
    };
    if progressive && position > 255 {
        return Err(Error::new_spanned(field, "position must be in 0..=255"));
    }
    Ok(Field {
        ident,
        ty: field.ty.clone(),
        name,
        position,
    })
}
