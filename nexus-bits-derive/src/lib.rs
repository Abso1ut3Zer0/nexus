use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Error, Result, Data, Fields, Ident, Type};

// =============================================================================
// IntEnum derive (existing)
// =============================================================================

#[proc_macro_derive(IntEnum)]
pub fn derive_int_enum(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    match derive_int_enum_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn derive_int_enum_impl(input: DeriveInput) -> Result<TokenStream2> {
    let variants = match &input.data {
        Data::Enum(data) => &data.variants,
        _ => return Err(Error::new_spanned(&input, "IntEnum can only be derived for enums")),
    };

    let repr = parse_repr(&input)?;

    for variant in variants {
        if !matches!(variant.fields, Fields::Unit) {
            return Err(Error::new_spanned(variant, "IntEnum variants cannot have fields"));
        }
    }

    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let from_arms = variants.iter().map(|v| {
        let variant_name = &v.ident;
        quote! {
            x if x == #name::#variant_name as #repr => Some(#name::#variant_name),
        }
    });

    Ok(quote! {
        impl #impl_generics nexus_bits::IntEnum for #name #ty_generics #where_clause {
            type Repr = #repr;

            #[inline]
            fn into_repr(self) -> #repr {
                self as #repr
            }

            #[inline]
            fn try_from_repr(repr: #repr) -> Option<Self> {
                match repr {
                    #(#from_arms)*
                    _ => None,
                }
            }
        }
    })
}

fn parse_repr(input: &DeriveInput) -> Result<Ident> {
    for attr in &input.attrs {
        if attr.path().is_ident("repr") {
            let repr: Ident = attr.parse_args()?;
            match repr.to_string().as_str() {
                "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" => {
                    return Ok(repr);
                }
                _ => {
                    return Err(Error::new_spanned(
                        repr,
                        "IntEnum requires repr(u8), repr(u16), repr(u32), repr(u64), repr(i8), repr(i16), repr(i32), or repr(i64)",
                    ));
                }
            }
        }
    }

    Err(Error::new_spanned(
        input,
        "IntEnum requires a #[repr(u8/u16/u32/u64/i8/i16/i32/i64)] attribute",
    ))
}

// =============================================================================
// BitPacked derive
// =============================================================================

#[proc_macro_derive(BitPacked, attributes(packed, field, flag, variant))]
pub fn derive_bit_packed(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    match derive_bit_packed_impl(input) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn derive_bit_packed_impl(input: DeriveInput) -> Result<TokenStream2> {
    match &input.data {
        Data::Struct(data) => derive_packed_struct(&input, data),
        Data::Enum(data) => derive_packed_enum(&input, data),
        Data::Union(_) => Err(Error::new_spanned(&input, "BitPacked cannot be derived for unions")),
    }
}

// =============================================================================
// Attribute types
// =============================================================================

/// Parsed #[packed(repr = T)] or #[packed(repr = T, discriminant(start = N, len = M))]
struct PackedAttr {
    repr: Ident,
    discriminant: Option<BitRange>,
}

/// Bit range for a field
struct BitRange {
    start: u32,
    len: u32,
}

/// Parsed field/flag from struct
enum MemberDef {
    Field {
        name: Ident,
        ty: Type,
        range: BitRange,
    },
    Flag {
        name: Ident,
        bit: u32,
    },
}

impl MemberDef {
    fn name(&self) -> &Ident {
        match self {
            MemberDef::Field { name, .. } => name,
            MemberDef::Flag { name, .. } => name,
        }
    }
}

// =============================================================================
// Attribute parsing
// =============================================================================

fn parse_packed_attr(attrs: &[syn::Attribute]) -> Result<PackedAttr> {
    for attr in attrs {
        if attr.path().is_ident("packed") {
            return parse_packed_attr_inner(attr);
        }
    }
    Err(Error::new(
        proc_macro2::Span::call_site(),
        "BitPacked requires a #[packed(repr = ...)] attribute",
    ))
}

fn parse_packed_attr_inner(attr: &syn::Attribute) -> Result<PackedAttr> {
    let mut repr = None;
    let mut discriminant = None;

    attr.parse_nested_meta(|meta| {
        if meta.path.is_ident("repr") {
            meta.input.parse::<syn::Token![=]>()?;
            repr = Some(meta.input.parse::<Ident>()?);
            Ok(())
        } else if meta.path.is_ident("discriminant") {
            let content;
            syn::parenthesized!(content in meta.input);
            discriminant = Some(parse_bit_range(&content)?);
            Ok(())
        } else {
            Err(meta.error("expected `repr` or `discriminant`"))
        }
    })?;

    let repr = repr.ok_or_else(|| Error::new_spanned(attr, "packed attribute requires `repr = ...`"))?;

    // Validate repr
    match repr.to_string().as_str() {
        "u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128" => {}
        _ => return Err(Error::new_spanned(&repr, "repr must be an integer type")),
    }

    Ok(PackedAttr { repr, discriminant })
}

fn parse_bit_range(input: syn::parse::ParseStream) -> Result<BitRange> {
    let mut start = None;
    let mut len = None;

    while !input.is_empty() {
        let ident: Ident = input.parse()?;
        input.parse::<syn::Token![=]>()?;
        let lit: syn::LitInt = input.parse()?;
        let value: u32 = lit.base10_parse()?;

        match ident.to_string().as_str() {
            "start" => start = Some(value),
            "len" => len = Some(value),
            _ => return Err(Error::new_spanned(ident, "expected `start` or `len`")),
        }

        if input.peek(syn::Token![,]) {
            input.parse::<syn::Token![,]>()?;
        }
    }

    let start = start.ok_or_else(|| Error::new(input.span(), "missing `start`"))?;
    let len = len.ok_or_else(|| Error::new(input.span(), "missing `len`"))?;

    if len == 0 {
        return Err(Error::new(input.span(), "len must be > 0"));
    }

    Ok(BitRange { start, len })
}

fn parse_member(field: &syn::Field) -> Result<MemberDef> {
    let name = field.ident.clone()
        .ok_or_else(|| Error::new_spanned(field, "tuple structs not supported"))?;
    let ty = field.ty.clone();

    for attr in &field.attrs {
        if attr.path().is_ident("field") {
            let range = attr.parse_args_with(parse_bit_range)?;
            return Ok(MemberDef::Field { name, ty, range });
        } else if attr.path().is_ident("flag") {
            let bit: syn::LitInt = attr.parse_args()?;
            let bit: u32 = bit.base10_parse()?;
            return Ok(MemberDef::Flag { name, bit });
        }
    }

    Err(Error::new_spanned(field, "field requires #[field(start = N, len = M)] or #[flag(N)] attribute"))
}

// =============================================================================
// Helpers
// =============================================================================

fn is_primitive(ty: &Type) -> bool {
    if let Type::Path(type_path) = ty {
        if let Some(ident) = type_path.path.get_ident() {
            return matches!(
                ident.to_string().as_str(),
                "u8" | "u16" | "u32" | "u64" | "u128" |
                "i8" | "i16" | "i32" | "i64" | "i128"
            );
        }
    }
    false
}

fn repr_bits(repr: &Ident) -> u32 {
    match repr.to_string().as_str() {
        "u8" | "i8" => 8,
        "u16" | "i16" => 16,
        "u32" | "i32" => 32,
        "u64" | "i64" => 64,
        "u128" | "i128" => 128,
        _ => 0,
    }
}

// =============================================================================
// Validation
// =============================================================================

fn validate_members(members: &[MemberDef], repr: &Ident) -> Result<()> {
    let bits = repr_bits(repr);

    // Check each field fits
    for member in members {
        match member {
            MemberDef::Field { name, range, .. } => {
                if range.start + range.len > bits {
                    return Err(Error::new_spanned(
                        name,
                        format!("field exceeds {} bits (start {} + len {} = {})", bits, range.start, range.len, range.start + range.len),
                    ));
                }
            }
            MemberDef::Flag { name, bit, .. } => {
                if *bit >= bits {
                    return Err(Error::new_spanned(
                        name,
                        format!("flag bit {} exceeds {} bits", bit, bits),
                    ));
                }
            }
        }
    }

    // Check no overlap (simple O(n²) for now)
    for (i, a) in members.iter().enumerate() {
        for b in members.iter().skip(i + 1) {
            if ranges_overlap(a, b) {
                return Err(Error::new_spanned(
                    b.name(),
                    format!("field '{}' overlaps with '{}'", b.name(), a.name()),
                ));
            }
        }
    }

    Ok(())
}

fn ranges_overlap(a: &MemberDef, b: &MemberDef) -> bool {
    let (a_start, a_end) = member_bit_range(a);
    let (b_start, b_end) = member_bit_range(b);
    a_start < b_end && b_start < a_end
}

fn member_bit_range(m: &MemberDef) -> (u32, u32) {
    match m {
        MemberDef::Field { range, .. } => (range.start, range.start + range.len),
        MemberDef::Flag { bit, .. } => (*bit, bit + 1),
    }
}

// =============================================================================
// Struct codegen
// =============================================================================

fn derive_packed_struct(input: &DeriveInput, data: &syn::DataStruct) -> Result<TokenStream2> {
    let fields = match &data.fields {
        Fields::Named(f) => &f.named,
        _ => return Err(Error::new_spanned(input, "BitPacked requires named fields")),
    };

    let packed_attr = parse_packed_attr(&input.attrs)?;

    if packed_attr.discriminant.is_some() {
        return Err(Error::new_spanned(input, "discriminant is only valid for enums"));
    }

    let members: Vec<MemberDef> = fields.iter()
        .map(parse_member)
        .collect::<Result<_>>()?;

    validate_members(&members, &packed_attr.repr)?;

    let name = &input.ident;
    let repr = &packed_attr.repr;
    let has_enum_fields = members.iter().any(|m| {
        matches!(m, MemberDef::Field { ty, .. } if !is_primitive(ty))
    });

    let pack_fn = generate_struct_pack(name, repr, &members);
    let unpack_fn = generate_struct_unpack(name, repr, &members, has_enum_fields);

    Ok(quote! {
        impl #name {
            #pack_fn
            #unpack_fn
        }
    })
}

fn generate_struct_pack(name: &Ident, repr: &Ident, members: &[MemberDef]) -> TokenStream2 {
    let pack_statements: Vec<TokenStream2> = members.iter().map(|m| {
        match m {
            MemberDef::Field { name: field_name, ty, range } => {
                let field_str = field_name.to_string();
                let start = range.start;
                let len = range.len;
                let max_val = if len >= 64 {
                    quote! { #repr::MAX }
                } else {
                    quote! { ((1 as #repr) << #len) - 1 }
                };

                if is_primitive(ty) {
                    quote! {
                        let field_val = self.#field_name as #repr;
                        if field_val > #max_val {
                            return Err(nexus_bits::FieldOverflow {
                                field: #field_str,
                                overflow: nexus_bits::Overflow { value: field_val, max: #max_val },
                            });
                        }
                        val |= field_val << #start;
                    }
                } else {
                    // IntEnum field
                    quote! {
                        let field_val = nexus_bits::IntEnum::into_repr(self.#field_name) as #repr;
                        if field_val > #max_val {
                            return Err(nexus_bits::FieldOverflow {
                                field: #field_str,
                                overflow: nexus_bits::Overflow { value: field_val, max: #max_val },
                            });
                        }
                        val |= field_val << #start;
                    }
                }
            }
            MemberDef::Flag { name: field_name, bit } => {
                quote! {
                    if self.#field_name {
                        val |= (1 as #repr) << #bit;
                    }
                }
            }
        }
    }).collect();

    quote! {
        /// Pack into integer representation.
        #[inline]
        pub fn pack(&self) -> Result<#repr, nexus_bits::FieldOverflow<#repr>> {
            let mut val: #repr = 0;
            #(#pack_statements)*
            Ok(val)
        }
    }
}

fn generate_struct_unpack(name: &Ident, repr: &Ident, members: &[MemberDef], has_enum_fields: bool) -> TokenStream2 {
    let unpack_statements: Vec<TokenStream2> = members.iter().map(|m| {
        match m {
            MemberDef::Field { name: field_name, ty, range } => {
                let start = range.start;
                let len = range.len;
                let mask = if len >= 64 {
                    quote! { #repr::MAX }
                } else {
                    quote! { ((1 as #repr) << #len) - 1 }
                };

                if is_primitive(ty) {
                    quote! {
                        let #field_name = ((raw >> #start) & #mask) as #ty;
                    }
                } else {
                    // IntEnum field
                    let field_str = field_name.to_string();
                    quote! {
                        let field_repr = ((raw >> #start) & #mask);
                        let #field_name = <#ty as nexus_bits::IntEnum>::try_from_repr(field_repr as _)
                            .ok_or(nexus_bits::UnknownDiscriminant {
                                field: #field_str,
                                value: raw,
                            })?;
                    }
                }
            }
            MemberDef::Flag { name: field_name, bit } => {
                quote! {
                    let #field_name = (raw >> #bit) & 1 != 0;
                }
            }
        }
    }).collect();

    let field_names: Vec<&Ident> = members.iter().map(|m| m.name()).collect();

    if has_enum_fields {
        quote! {
            /// Unpack from integer representation.
            #[inline]
            pub fn unpack(raw: #repr) -> Result<Self, nexus_bits::UnknownDiscriminant<#repr>> {
                #(#unpack_statements)*
                Ok(Self { #(#field_names),* })
            }
        }
    } else {
        quote! {
            /// Unpack from integer representation.
            #[inline]
            pub fn unpack(raw: #repr) -> Self {
                #(#unpack_statements)*
                Self { #(#field_names),* }
            }
        }
    }
}

// =============================================================================
// Enum codegen (placeholder)
// =============================================================================

fn derive_packed_enum(input: &DeriveInput, _data: &syn::DataEnum) -> Result<TokenStream2> {
    Err(Error::new_spanned(input, "BitPacked for enums not yet implemented"))
}
