use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{
    Data, DeriveInput, Error, Fields, Ident, Result, Type, parse::Parser, parse_macro_input,
};

// =============================================================================
// IntEnum derive
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
        _ => {
            return Err(Error::new_spanned(
                &input,
                "IntEnum can only be derived for enums",
            ));
        }
    };

    let repr = parse_repr(&input)?;

    for variant in variants {
        if !matches!(variant.fields, Fields::Unit) {
            return Err(Error::new_spanned(
                variant,
                "IntEnum variants cannot have fields",
            ));
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
// BitStorage attribute macro
// =============================================================================

#[proc_macro_attribute]
pub fn bit_storage(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = proc_macro2::TokenStream::from(attr);
    let item = parse_macro_input!(item as DeriveInput);

    match bit_storage_impl(attr, item) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

fn bit_storage_impl(attr: TokenStream2, input: DeriveInput) -> Result<TokenStream2> {
    let storage_attr = parse_storage_attr_tokens(attr)?;

    match &input.data {
        Data::Struct(data) => derive_storage_struct(&input, data, storage_attr),
        Data::Enum(data) => derive_storage_enum(&input, data, storage_attr),
        Data::Union(_) => Err(Error::new_spanned(
            &input,
            "bit_storage cannot be applied to unions",
        )),
    }
}

// =============================================================================
// Attribute types
// =============================================================================

/// Parsed #[bit_storage(repr = T)] or #[bit_storage(repr = T, discriminant(start = N, len = M))]
struct StorageAttr {
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

fn parse_storage_attr_tokens(attr: TokenStream2) -> Result<StorageAttr> {
    let mut repr = None;
    let mut discriminant = None;

    let parser = syn::meta::parser(|meta| {
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
    });

    parser.parse2(attr)?;

    let repr = repr.ok_or_else(|| {
        Error::new(
            proc_macro2::Span::call_site(),
            "bit_storage requires `repr = ...`",
        )
    })?;

    // Validate repr
    match repr.to_string().as_str() {
        "u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128" => {}
        _ => return Err(Error::new_spanned(&repr, "repr must be an integer type")),
    }

    Ok(StorageAttr { repr, discriminant })
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
    let name = field
        .ident
        .clone()
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

    Err(Error::new_spanned(
        field,
        "field requires #[field(start = N, len = M)] or #[flag(N)] attribute",
    ))
}

fn parse_variant_attr(attrs: &[syn::Attribute]) -> Result<u64> {
    for attr in attrs {
        if attr.path().is_ident("variant") {
            let lit: syn::LitInt = attr.parse_args()?;
            return lit.base10_parse();
        }
    }
    Err(Error::new(
        proc_macro2::Span::call_site(),
        "enum variant requires #[variant(N)] attribute",
    ))
}

// =============================================================================
// Helpers
// =============================================================================

fn is_primitive(ty: &Type) -> bool {
    if let Type::Path(type_path) = ty {
        if let Some(ident) = type_path.path.get_ident() {
            return matches!(
                ident.to_string().as_str(),
                "u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128"
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
                        format!(
                            "field exceeds {} bits (start {} + len {} = {})",
                            bits,
                            range.start,
                            range.len,
                            range.start + range.len
                        ),
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

fn derive_storage_struct(
    input: &DeriveInput,
    data: &syn::DataStruct,
    storage_attr: StorageAttr,
) -> Result<TokenStream2> {
    let fields = match &data.fields {
        Fields::Named(f) => &f.named,
        _ => {
            return Err(Error::new_spanned(
                input,
                "bit_storage requires named fields",
            ));
        }
    };

    if storage_attr.discriminant.is_some() {
        return Err(Error::new_spanned(
            input,
            "discriminant is only valid for enums",
        ));
    }

    let members: Vec<MemberDef> = fields.iter().map(parse_member).collect::<Result<_>>()?;

    validate_members(&members, &storage_attr.repr)?;

    let vis = &input.vis;
    let name = &input.ident;
    let repr = &storage_attr.repr;
    let builder_name = Ident::new(&format!("{}Builder", name), name.span());

    let newtype = generate_struct_newtype(vis, name, repr);
    let builder_struct = generate_struct_builder_struct(vis, &builder_name, &members);
    let newtype_impl = generate_struct_newtype_impl(name, &builder_name, repr, &members);
    let builder_impl = generate_struct_builder_impl(name, &builder_name, repr, &members);

    Ok(quote! {
        #newtype
        #builder_struct
        #newtype_impl
        #builder_impl
    })
}

fn generate_struct_newtype(vis: &syn::Visibility, name: &Ident, repr: &Ident) -> TokenStream2 {
    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        #vis struct #name(#vis #repr);
    }
}

fn generate_struct_builder_struct(
    vis: &syn::Visibility,
    builder_name: &Ident,
    members: &[MemberDef],
) -> TokenStream2 {
    let fields: Vec<TokenStream2> = members
        .iter()
        .map(|m| match m {
            MemberDef::Field { name, ty, .. } => {
                quote! { #name: Option<#ty>, }
            }
            MemberDef::Flag { name, .. } => {
                quote! { #name: Option<bool>, }
            }
        })
        .collect();

    quote! {
        #[derive(Debug, Clone, Copy, Default)]
        #vis struct #builder_name {
            #(#fields)*
        }
    }
}

fn generate_struct_newtype_impl(
    name: &Ident,
    builder_name: &Ident,
    repr: &Ident,
    members: &[MemberDef],
) -> TokenStream2 {
    let repr_bit_count = repr_bits(repr);

    let accessors: Vec<TokenStream2> = members.iter().map(|m| {
        match m {
            MemberDef::Field { name: field_name, ty, range } => {
                let start = range.start;
                let len = range.len;
                let mask = if len >= repr_bit_count {
                    quote! { #repr::MAX }
                } else {
                    quote! { ((1 as #repr) << #len) - 1 }
                };

                if is_primitive(ty) {
                    quote! {
                        #[inline]
                        pub const fn #field_name(&self) -> #ty {
                            ((self.0 >> #start) & #mask) as #ty
                        }
                    }
                } else {
                    // IntEnum field - returns Result
                    quote! {
                        #[inline]
                        pub fn #field_name(&self) -> Result<#ty, nexus_bits::UnknownDiscriminant<#repr>> {
                            let field_repr = ((self.0 >> #start) & #mask);
                            <#ty as nexus_bits::IntEnum>::try_from_repr(field_repr as _)
                                .ok_or(nexus_bits::UnknownDiscriminant {
                                    field: stringify!(#field_name),
                                    value: self.0,
                                })
                        }
                    }
                }
            }
            MemberDef::Flag { name: field_name, bit } => {
                quote! {
                    #[inline]
                    pub const fn #field_name(&self) -> bool {
                        (self.0 >> #bit) & 1 != 0
                    }
                }
            }
        }
    }).collect();

    quote! {
        impl #name {
            /// Create from raw integer value.
            #[inline]
            pub const fn from_raw(raw: #repr) -> Self {
                Self(raw)
            }

            /// Get the raw integer value.
            #[inline]
            pub const fn raw(self) -> #repr {
                self.0
            }

            /// Create a builder for this type.
            #[inline]
            pub fn builder() -> #builder_name {
                #builder_name::default()
            }

            #(#accessors)*
        }
    }
}

fn generate_struct_builder_impl(
    name: &Ident,
    builder_name: &Ident,
    repr: &Ident,
    members: &[MemberDef],
) -> TokenStream2 {
    let repr_bit_count = repr_bits(repr);

    // Setters - wrap in Some
    let setters: Vec<TokenStream2> = members
        .iter()
        .map(|m| match m {
            MemberDef::Field {
                name: field_name,
                ty,
                ..
            } => {
                quote! {
                    #[inline]
                    pub fn #field_name(mut self, val: #ty) -> Self {
                        self.#field_name = Some(val);
                        self
                    }
                }
            }
            MemberDef::Flag {
                name: field_name, ..
            } => {
                quote! {
                    #[inline]
                    pub fn #field_name(mut self, val: bool) -> Self {
                        self.#field_name = Some(val);
                        self
                    }
                }
            }
        })
        .collect();

    // Validations - only for primitive fields that could overflow
    let validations: Vec<TokenStream2> = members
        .iter()
        .filter_map(|m| match m {
            MemberDef::Field {
                name: field_name,
                ty,
                range,
            } if is_primitive(ty) => {
                let field_str = field_name.to_string();
                let len = range.len;

                let type_bits: u32 = match ty {
                    Type::Path(p) if p.path.is_ident("u8") || p.path.is_ident("i8") => 8,
                    Type::Path(p) if p.path.is_ident("u16") || p.path.is_ident("i16") => 16,
                    Type::Path(p) if p.path.is_ident("u32") || p.path.is_ident("i32") => 32,
                    Type::Path(p) if p.path.is_ident("u64") || p.path.is_ident("i64") => 64,
                    Type::Path(p) if p.path.is_ident("u128") || p.path.is_ident("i128") => 128,
                    _ => 128,
                };

                if len >= type_bits {
                    return None;
                }

                let max_val = if len >= repr_bit_count {
                    quote! { #repr::MAX }
                } else {
                    quote! { ((1 as #repr) << #len) - 1 }
                };

                Some(quote! {
                    if let Some(v) = self.#field_name {
                        if (v as #repr) > #max_val {
                            return Err(nexus_bits::FieldOverflow {
                                field: #field_str,
                                overflow: nexus_bits::Overflow {
                                    value: v as #repr,
                                    max: #max_val,
                                },
                            });
                        }
                    }
                })
            }
            _ => None,
        })
        .collect();

    // Pack statements - only pack if Some
    let pack_statements: Vec<TokenStream2> = members
        .iter()
        .map(|m| {
            match m {
                MemberDef::Field {
                    name: field_name,
                    ty,
                    range,
                } => {
                    let start = range.start;

                    if is_primitive(ty) {
                        quote! {
                            if let Some(v) = self.#field_name {
                                val |= (v as #repr) << #start;
                            }
                        }
                    } else {
                        // IntEnum
                        quote! {
                            if let Some(v) = self.#field_name {
                                val |= (nexus_bits::IntEnum::into_repr(v) as #repr) << #start;
                            }
                        }
                    }
                }
                MemberDef::Flag {
                    name: field_name,
                    bit,
                } => {
                    quote! {
                        if let Some(true) = self.#field_name {
                            val |= (1 as #repr) << #bit;
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        impl #builder_name {
            #(#setters)*

            /// Build the final value, validating all fields.
            #[inline]
            pub fn build(self) -> Result<#name, nexus_bits::FieldOverflow<#repr>> {
                // Validate
                #(#validations)*

                // Pack
                let mut val: #repr = 0;
                #(#pack_statements)*

                Ok(#name(val))
            }
        }
    }
}

// =============================================================================
// Enum codegen
// =============================================================================

/// Parsed variant for tagged enum
struct ParsedVariant {
    name: Ident,
    discriminant: u64,
}

fn derive_storage_enum(
    input: &DeriveInput,
    data: &syn::DataEnum,
    storage_attr: StorageAttr,
) -> Result<TokenStream2> {
    let discriminant = storage_attr.discriminant.ok_or_else(|| {
        Error::new_spanned(
            input,
            "bit_storage enum requires discriminant: #[bit_storage(repr = T, discriminant(start = N, len = M))]",
        )
    })?;

    let repr = &storage_attr.repr;
    let bits = repr_bits(repr);

    // Validate discriminant fits
    if discriminant.start + discriminant.len > bits {
        return Err(Error::new_spanned(
            input,
            format!(
                "discriminant exceeds {} bits (start {} + len {} = {})",
                bits,
                discriminant.start,
                discriminant.len,
                discriminant.start + discriminant.len
            ),
        ));
    }

    let max_discriminant = if discriminant.len >= 64 {
        u64::MAX
    } else {
        (1u64 << discriminant.len) - 1
    };

    // Parse all variants
    let mut variants = Vec::new();
    for variant in &data.variants {
        let disc = parse_variant_attr(&variant.attrs)?;

        if disc > max_discriminant {
            return Err(Error::new_spanned(
                &variant.ident,
                format!(
                    "variant discriminant {} exceeds max {} for {}-bit field",
                    disc, max_discriminant, discriminant.len
                ),
            ));
        }

        // Check for duplicate discriminants
        for existing in &variants {
            let existing: &ParsedVariant = existing;
            if existing.discriminant == disc {
                return Err(Error::new_spanned(
                    &variant.ident,
                    format!(
                        "duplicate discriminant {}: already used by '{}'",
                        disc, existing.name
                    ),
                ));
            }
        }

        let members: Vec<MemberDef> = match &variant.fields {
            Fields::Named(fields) => fields
                .named
                .iter()
                .map(parse_member)
                .collect::<Result<_>>()?,
            Fields::Unit => Vec::new(),
            Fields::Unnamed(_) => {
                return Err(Error::new_spanned(
                    variant,
                    "tuple variants not supported, use named fields",
                ));
            }
        };

        // Validate members don't overlap with discriminant
        let disc_range = MemberDef::Field {
            name: Ident::new("__discriminant", proc_macro2::Span::call_site()),
            ty: syn::parse_quote!(u64),
            range: BitRange {
                start: discriminant.start,
                len: discriminant.len,
            },
        };

        for member in &members {
            if ranges_overlap(&disc_range, member) {
                return Err(Error::new_spanned(
                    member.name(),
                    format!("field '{}' overlaps with discriminant", member.name()),
                ));
            }
        }

        // Validate members within this variant
        validate_members(&members, repr)?;

        variants.push(ParsedVariant {
            name: variant.ident.clone(),
            discriminant: disc,
        });
    }

    let _vis = &input.vis;
    let _name = &input.ident;
    let _discriminant = discriminant;
    let _variants = variants;

    // TODO: generate parent type, variant types, Kind enum, impls, builders, accessors
    todo!("enum codegen not yet implemented")
}
