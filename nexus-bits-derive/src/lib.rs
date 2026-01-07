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

    // Validations
    let validations: Vec<TokenStream2> = members
        .iter()
        .filter_map(|m| match m {
            MemberDef::Field {
                name: field_name,
                ty,
                range,
            } => {
                let field_str = field_name.to_string();
                let len = range.len;

                let max_val = if len >= repr_bit_count {
                    quote! { #repr::MAX }
                } else {
                    quote! { ((1 as #repr) << #len) - 1 }
                };

                if is_primitive(ty) {
                    let type_bits: u32 = match ty {
                        Type::Path(p) if p.path.is_ident("u8") || p.path.is_ident("i8") => 8,
                        Type::Path(p) if p.path.is_ident("u16") || p.path.is_ident("i16") => 16,
                        Type::Path(p) if p.path.is_ident("u32") || p.path.is_ident("i32") => 32,
                        Type::Path(p) if p.path.is_ident("u64") || p.path.is_ident("i64") => 64,
                        Type::Path(p) if p.path.is_ident("u128") || p.path.is_ident("i128") => 128,
                        _ => 128,
                    };

                    // Skip validation if field can hold entire type
                    if len >= type_bits {
                        return None;
                    }

                    // Check if this is a signed type
                    let is_signed = matches!(ty,
                        Type::Path(p) if p.path.is_ident("i8") || p.path.is_ident("i16") ||
                                         p.path.is_ident("i32") || p.path.is_ident("i64") ||
                                         p.path.is_ident("i128")
                    );

                    if is_signed {
                        // For signed types, check that value fits in signed field range
                        // A signed N-bit field can hold -(2^(N-1)) to (2^(N-1) - 1)
                        let min_shift = len - 1;
                        Some(quote! {
                            if let Some(v) = self.#field_name {
                                let min_val = -((1i128 << #min_shift) as i128);
                                let max_val = ((1i128 << #min_shift) - 1) as i128;
                                let v_i128 = v as i128;
                                if v_i128 < min_val || v_i128 > max_val {
                                    return Err(nexus_bits::FieldOverflow {
                                        field: #field_str,
                                        overflow: nexus_bits::Overflow {
                                            value: (v as #repr),
                                            max: #max_val,
                                        },
                                    });
                                }
                            }
                        })
                    } else {
                        // Unsigned - simple max check
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
                } else {
                    // IntEnum field - validate repr value fits in field
                    Some(quote! {
                        if let Some(v) = self.#field_name {
                            let repr_val = nexus_bits::IntEnum::into_repr(v) as #repr;
                            if repr_val > #max_val {
                                return Err(nexus_bits::FieldOverflow {
                                    field: #field_str,
                                    overflow: nexus_bits::Overflow {
                                        value: repr_val,
                                        max: #max_val,
                                    },
                                });
                            }
                        }
                    })
                }
            }
            _ => None,
        })
        .collect();

    // Pack statements - ALWAYS mask to prevent sign extension corruption
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
                    let len = range.len;
                    let mask = if len >= repr_bit_count {
                        quote! { #repr::MAX }
                    } else {
                        quote! { ((1 as #repr) << #len) - 1 }
                    };

                    if is_primitive(ty) {
                        quote! {
                            if let Some(v) = self.#field_name {
                                val |= ((v as #repr) & #mask) << #start;
                            }
                        }
                    } else {
                        // IntEnum
                        quote! {
                            if let Some(v) = self.#field_name {
                                val |= ((nexus_bits::IntEnum::into_repr(v) as #repr) & #mask) << #start;
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
    members: Vec<MemberDef>,
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
            members,
        });
    }

    let vis = &input.vis;
    let name = &input.ident;

    let parent_type = generate_enum_parent_type(vis, name, repr);
    let variant_types = generate_enum_variant_types(vis, name, repr, &variants);
    let kind_enum = generate_enum_kind(vis, name, &variants);
    let builder_structs = generate_enum_builder_structs(vis, name, &variants);
    let parent_impl = generate_enum_parent_impl(name, repr, &discriminant, &variants);
    let variant_impls = generate_enum_variant_impls(name, repr, &variants);
    let builder_impls = generate_enum_builder_impls(name, repr, &discriminant, &variants);
    let from_impls = generate_enum_from_impls(name, &variants);

    Ok(quote! {
        #parent_type
        #variant_types
        #kind_enum
        #builder_structs
        #parent_impl
        #variant_impls
        #builder_impls
        #from_impls
    })
}

fn variant_type_name(parent_name: &Ident, variant_name: &Ident) -> Ident {
    Ident::new(
        &format!("{}{}", parent_name, variant_name),
        variant_name.span(),
    )
}

fn variant_builder_name(parent_name: &Ident, variant_name: &Ident) -> Ident {
    Ident::new(
        &format!("{}{}Builder", parent_name, variant_name),
        variant_name.span(),
    )
}

fn kind_enum_name(parent_name: &Ident) -> Ident {
    Ident::new(&format!("{}Kind", parent_name), parent_name.span())
}

fn generate_enum_parent_type(vis: &syn::Visibility, name: &Ident, repr: &Ident) -> TokenStream2 {
    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(transparent)]
        #vis struct #name(#vis #repr);
    }
}

fn generate_enum_variant_types(
    vis: &syn::Visibility,
    parent_name: &Ident,
    repr: &Ident,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let types: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let type_name = variant_type_name(parent_name, &v.name);
            quote! {
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                #[repr(transparent)]
                #vis struct #type_name(#repr);
            }
        })
        .collect();

    quote! { #(#types)* }
}

fn generate_enum_kind(
    vis: &syn::Visibility,
    parent_name: &Ident,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let kind_name = kind_enum_name(parent_name);
    let variant_names: Vec<&Ident> = variants.iter().map(|v| &v.name).collect();

    quote! {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #vis enum #kind_name {
            #(#variant_names),*
        }
    }
}

fn generate_enum_builder_structs(
    vis: &syn::Visibility,
    parent_name: &Ident,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let builders: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let builder_name = variant_builder_name(parent_name, &v.name);

            let fields: Vec<TokenStream2> = v
                .members
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
        })
        .collect();

    quote! { #(#builders)* }
}

fn generate_enum_parent_impl(
    name: &Ident,
    repr: &Ident,
    discriminant: &BitRange,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let repr_bit_count = repr_bits(repr);
    let kind_name = kind_enum_name(name);
    let disc_start = discriminant.start;
    let disc_len = discriminant.len;

    let disc_mask = if disc_len >= repr_bit_count {
        quote! { #repr::MAX }
    } else {
        quote! { ((1 as #repr) << #disc_len) - 1 }
    };

    // kind() match arms
    let kind_arms: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.name;
            let disc_val = v.discriminant;
            quote! {
                #disc_val => Ok(#kind_name::#variant_name),
            }
        })
        .collect();

    // is_* methods
    let is_methods: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.name;
            let method_name = Ident::new(
                &format!("is_{}", to_snake_case(&variant_name.to_string())),
                variant_name.span(),
            );
            let disc_val = v.discriminant;
            quote! {
                #[inline]
                pub fn #method_name(&self) -> bool {
                    let disc = ((self.0 >> #disc_start) & #disc_mask) as u64;
                    disc == #disc_val
                }
            }
        })
        .collect();

    // as_* methods
    let as_methods: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.name;
            let variant_type = variant_type_name(name, variant_name);
            let method_name = Ident::new(
                &format!("as_{}", to_snake_case(&variant_name.to_string())),
                variant_name.span(),
            );
            let disc_val = v.discriminant;

            // Validation for IntEnum fields
            let validations: Vec<TokenStream2> = v.members
                .iter()
                .filter_map(|m| {
                    if let MemberDef::Field { name: field_name, ty, range } = m {
                        if !is_primitive(ty) {
                            let start = range.start;
                            let len = range.len;
                            let repr_bit_count = repr_bits(repr);
                            let mask = if len >= repr_bit_count {
                                quote! { #repr::MAX }
                            } else {
                                quote! { ((1 as #repr) << #len) - 1 }
                            };
                            return Some(quote! {
                                let field_repr = ((self.0 >> #start) & #mask);
                                if <#ty as nexus_bits::IntEnum>::try_from_repr(field_repr as _).is_none() {
                                    return Err(nexus_bits::UnknownDiscriminant {
                                        field: stringify!(#field_name),
                                        value: self.0,
                                    });
                                }
                            });
                        }
                    }
                    None
                })
                .collect();

            quote! {
                #[inline]
                pub fn #method_name(&self) -> Result<#variant_type, nexus_bits::UnknownDiscriminant<#repr>> {
                    let disc = ((self.0 >> #disc_start) & #disc_mask) as u64;
                    if disc != #disc_val {
                        return Err(nexus_bits::UnknownDiscriminant {
                            field: "__discriminant",
                            value: self.0,
                        });
                    }
                    #(#validations)*
                    Ok(#variant_type(self.0))
                }
            }
        })
        .collect();

    // Builder shortcut methods
    let builder_methods: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.name;
            let builder_name = variant_builder_name(name, variant_name);
            let method_name = Ident::new(
                &to_snake_case(&variant_name.to_string()),
                variant_name.span(),
            );
            quote! {
                #[inline]
                pub fn #method_name() -> #builder_name {
                    #builder_name::default()
                }
            }
        })
        .collect();

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

            /// Get the kind (discriminant) of this value.
            #[inline]
            pub fn kind(&self) -> Result<#kind_name, nexus_bits::UnknownDiscriminant<#repr>> {
                let disc = ((self.0 >> #disc_start) & #disc_mask) as u64;
                match disc {
                    #(#kind_arms)*
                    _ => Err(nexus_bits::UnknownDiscriminant {
                        field: "__discriminant",
                        value: self.0,
                    }),
                }
            }

            #(#is_methods)*

            #(#as_methods)*

            #(#builder_methods)*
        }
    }
}

fn generate_enum_variant_impls(
    parent_name: &Ident,
    repr: &Ident,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let repr_bit_count = repr_bits(repr);

    let impls: Vec<TokenStream2> =
        variants
            .iter()
            .map(|v| {
                let variant_name = &v.name;
                let variant_type = variant_type_name(parent_name, variant_name);
                let builder_name = variant_builder_name(parent_name, variant_name);

                // Accessors - infallible since variant is pre-validated
                let accessors: Vec<TokenStream2> = v.members
                .iter()
                .map(|m| {
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
                                // IntEnum - infallible because already validated
                                quote! {
                                    #[inline]
                                    pub fn #field_name(&self) -> #ty {
                                        let field_repr = ((self.0 >> #start) & #mask);
                                        // SAFETY: This type was validated during construction
                                        <#ty as nexus_bits::IntEnum>::try_from_repr(field_repr as _)
                                            .expect("variant type invariant violated")
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
                })
                .collect();

                quote! {
                    impl #variant_type {
                        /// Create a builder for this variant.
                        #[inline]
                        pub fn builder() -> #builder_name {
                            #builder_name::default()
                        }

                        /// Get the raw integer value.
                        #[inline]
                        pub const fn raw(self) -> #repr {
                            self.0
                        }

                        /// Convert to parent type.
                        #[inline]
                        pub const fn as_parent(self) -> #parent_name {
                            #parent_name(self.0)
                        }

                        #(#accessors)*
                    }
                }
            })
            .collect();

    quote! { #(#impls)* }
}

fn generate_enum_builder_impls(
    parent_name: &Ident,
    repr: &Ident,
    discriminant: &BitRange,
    variants: &[ParsedVariant],
) -> TokenStream2 {
    let repr_bit_count = repr_bits(repr);
    let disc_start = discriminant.start;

    let impls: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_name = &v.name;
            let variant_type = variant_type_name(parent_name, variant_name);
            let builder_name = variant_builder_name(parent_name, variant_name);
            let disc_val = v.discriminant;

            // Setters
            let setters: Vec<TokenStream2> = v.members
                .iter()
                .map(|m| match m {
                    MemberDef::Field { name: field_name, ty, .. } => {
                        quote! {
                            #[inline]
                            pub fn #field_name(mut self, val: #ty) -> Self {
                                self.#field_name = Some(val);
                                self
                            }
                        }
                    }
                    MemberDef::Flag { name: field_name, .. } => {
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

            // Validations
            let validations: Vec<TokenStream2> = v.members
                .iter()
                .filter_map(|m| match m {
                    MemberDef::Field { name: field_name, ty, range } => {
                        let field_str = field_name.to_string();
                        let len = range.len;

                        let max_val = if len >= repr_bit_count {
                            quote! { #repr::MAX }
                        } else {
                            quote! { ((1 as #repr) << #len) - 1 }
                        };

                        if is_primitive(ty) {
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

                            let is_signed = matches!(ty,
                                Type::Path(p) if p.path.is_ident("i8") || p.path.is_ident("i16") ||
                                                 p.path.is_ident("i32") || p.path.is_ident("i64") ||
                                                 p.path.is_ident("i128")
                            );

                            if is_signed {
                                let min_shift = len - 1;
                                Some(quote! {
                                    if let Some(v) = self.#field_name {
                                        let min_val = -((1i128 << #min_shift) as i128);
                                        let max_val = ((1i128 << #min_shift) - 1) as i128;
                                        let v_i128 = v as i128;
                                        if v_i128 < min_val || v_i128 > max_val {
                                            return Err(nexus_bits::FieldOverflow {
                                                field: #field_str,
                                                overflow: nexus_bits::Overflow {
                                                    value: (v as #repr),
                                                    max: #max_val,
                                                },
                                            });
                                        }
                                    }
                                })
                            } else {
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
                        } else {
                            // IntEnum field
                            Some(quote! {
                                if let Some(v) = self.#field_name {
                                    let repr_val = nexus_bits::IntEnum::into_repr(v) as #repr;
                                    if repr_val > #max_val {
                                        return Err(nexus_bits::FieldOverflow {
                                            field: #field_str,
                                            overflow: nexus_bits::Overflow {
                                                value: repr_val,
                                                max: #max_val,
                                            },
                                        });
                                    }
                                }
                            })
                        }
                    }
                    _ => None,
                })
                .collect();

            // Pack statements
            let pack_statements: Vec<TokenStream2> = v.members
                .iter()
                .map(|m| {
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
                                    if let Some(v) = self.#field_name {
                                        val |= ((v as #repr) & #mask) << #start;
                                    }
                                }
                            } else {
                                quote! {
                                    if let Some(v) = self.#field_name {
                                        val |= ((nexus_bits::IntEnum::into_repr(v) as #repr) & #mask) << #start;
                                    }
                                }
                            }
                        }
                        MemberDef::Flag { name: field_name, bit } => {
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

                    /// Build the variant type, validating all fields.
                    #[inline]
                    pub fn build(self) -> Result<#variant_type, nexus_bits::FieldOverflow<#repr>> {
                        #(#validations)*

                        let mut val: #repr = 0;
                        // Set discriminant
                        val |= (#disc_val as #repr) << #disc_start;
                        #(#pack_statements)*

                        Ok(#variant_type(val))
                    }

                    /// Build directly to parent type, validating all fields.
                    #[inline]
                    pub fn build_parent(self) -> Result<#parent_name, nexus_bits::FieldOverflow<#repr>> {
                        self.build().map(|v| v.as_parent())
                    }
                }
            }
        })
        .collect();

    quote! { #(#impls)* }
}

fn generate_enum_from_impls(parent_name: &Ident, variants: &[ParsedVariant]) -> TokenStream2 {
    let impls: Vec<TokenStream2> = variants
        .iter()
        .map(|v| {
            let variant_type = variant_type_name(parent_name, &v.name);
            quote! {
                impl From<#variant_type> for #parent_name {
                    #[inline]
                    fn from(v: #variant_type) -> Self {
                        v.as_parent()
                    }
                }
            }
        })
        .collect();

    quote! { #(#impls)* }
}

fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() {
            if i > 0 {
                result.push('_');
            }
            result.push(c.to_lowercase().next().unwrap());
        } else {
            result.push(c);
        }
    }
    result
}
