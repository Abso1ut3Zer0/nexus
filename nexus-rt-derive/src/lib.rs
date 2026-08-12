//! Derive macros for nexus-rt.
//!
//! Use `nexus-rt` instead of depending on this crate directly.
//! The derives are re-exported from `nexus_rt::{Resource, Deref, DerefMut, select}`.

#![warn(missing_docs)]

mod select;

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::visit_mut::VisitMut;
use syn::{Data, DeriveInput, Fields, GenericParam, Lifetime, TypeParamBound, parse_macro_input};

// =============================================================================
// #[derive(Resource)]
// =============================================================================

/// Derive the `Resource` marker trait, allowing this type to be stored
/// in a `World`.
///
/// ```ignore
/// use nexus_rt::Resource;
///
/// #[derive(Resource)]
/// struct OrderBook {
///     bids: Vec<(f64, f64)>,
///     asks: Vec<(f64, f64)>,
/// }
/// ```
#[proc_macro_derive(Resource)]
pub fn derive_resource(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    // The `Resource: Send + 'static` supertrait is what actually enforces the
    // bound. How we express the impl depends on whether the type is generic:
    //
    // - CONCRETE type: rely on the supertrait alone (no explicit predicate). It
    //   still reports a genuinely non-Send type at the derive site, and — unlike
    //   an explicit predicate — is discharged coinductively, so it does NOT
    //   overflow on self-referential resources such as a timer-wheel slot
    //   `struct Pending(Option<TemplatedCallback<K>>)`. (An explicit
    //   `where Self: Send + 'static` forces `Send` to be proven eagerly and
    //   overflows on that shape.)
    // - GENERIC type: add `where Self: Send + 'static` so the impl is
    //   *conditional*. Without it, an unconditional `impl<T> Resource for Foo<T>`
    //   would require EVERY instantiation to be Send + 'static and reject e.g.
    //   `Foo<Rc<_>>`. With it, `Foo<T>` is a `Resource` exactly when it is
    //   Send + 'static.
    let where_clause = if input.generics.params.is_empty() {
        where_clause.cloned()
    } else {
        let mut bounds = where_clause.cloned();
        let predicate: syn::WherePredicate = syn::parse_quote!(#name #ty_generics: Send + 'static);
        bounds
            .get_or_insert_with(|| syn::parse_quote!(where))
            .predicates
            .push(predicate);
        bounds
    };

    quote! {
        impl #impl_generics ::nexus_rt::Resource for #name #ty_generics
            #where_clause
        {}
    }
    .into()
}

// =============================================================================
// #[derive(Deref)]
// =============================================================================

/// Derive `Deref` for newtype wrappers.
///
/// - Single-field structs: auto-selects the field.
/// - Multi-field structs: requires `#[deref]` on exactly one field.
///
/// ```ignore
/// use nexus_rt::Deref;
///
/// #[derive(Deref)]
/// struct MyWrapper(u64);
///
/// #[derive(Deref)]
/// struct Named {
///     #[deref]
///     data: Vec<u8>,
///     label: String,
/// }
/// ```
#[proc_macro_derive(Deref, attributes(deref))]
pub fn derive_deref(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let (field_ty, field_access) = match deref_field(&input.data, name) {
        Ok(v) => v,
        Err(e) => return e.to_compile_error().into(),
    };

    quote! {
        impl #impl_generics ::core::ops::Deref for #name #ty_generics
            #where_clause
        {
            type Target = #field_ty;

            #[inline]
            fn deref(&self) -> &Self::Target {
                &self.#field_access
            }
        }
    }
    .into()
}

// =============================================================================
// #[derive(DerefMut)]
// =============================================================================

/// Derive `DerefMut` for newtype wrappers.
///
/// Same field selection rules as `#[derive(Deref)]`. Must be used
/// alongside `#[derive(Deref)]`.
#[proc_macro_derive(DerefMut, attributes(deref))]
pub fn derive_deref_mut(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let (_field_ty, field_access) = match deref_field(&input.data, name) {
        Ok(v) => v,
        Err(e) => return e.to_compile_error().into(),
    };

    quote! {
        impl #impl_generics ::core::ops::DerefMut for #name #ty_generics
            #where_clause
        {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.#field_access
            }
        }
    }
    .into()
}

// =============================================================================
// Shared field resolution
// =============================================================================

/// Find the deref target field. Returns (field_type, field_access).
fn deref_field(
    data: &Data,
    name: &syn::Ident,
) -> Result<(syn::Type, proc_macro2::TokenStream), syn::Error> {
    let fields = match data {
        Data::Struct(s) => &s.fields,
        Data::Enum(_) => {
            return Err(syn::Error::new_spanned(
                name,
                "Deref/DerefMut can only be derived for structs, not enums",
            ));
        }
        Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                name,
                "Deref/DerefMut can only be derived for structs, not unions",
            ));
        }
    };

    match fields {
        // Tuple struct: single field → auto-select
        Fields::Unnamed(f) if f.unnamed.len() == 1 => {
            let field = f.unnamed.first().unwrap();
            let ty = field.ty.clone();
            let access = quote!(0);
            Ok((ty, access))
        }
        // Named struct: single field → auto-select
        Fields::Named(f) if f.named.len() == 1 => {
            let field = f.named.first().unwrap();
            let ty = field.ty.clone();
            let ident = field.ident.as_ref().unwrap();
            let access = quote!(#ident);
            Ok((ty, access))
        }
        // Multiple fields → look for #[deref] attribute
        Fields::Named(f) => {
            let marked: Vec<_> = f
                .named
                .iter()
                .filter(|field| field.attrs.iter().any(|a| a.path().is_ident("deref")))
                .collect();

            match marked.len() {
                0 => Err(syn::Error::new_spanned(
                    name,
                    "multiple fields require exactly one `#[deref]` attribute",
                )),
                1 => {
                    let field = marked[0];
                    let ty = field.ty.clone();
                    let ident = field.ident.as_ref().unwrap();
                    let access = quote!(#ident);
                    Ok((ty, access))
                }
                _ => Err(syn::Error::new_spanned(
                    name,
                    "only one field may have `#[deref]`",
                )),
            }
        }
        Fields::Unnamed(f) => {
            let marked: Vec<_> = f
                .unnamed
                .iter()
                .enumerate()
                .filter(|(_, field)| field.attrs.iter().any(|a| a.path().is_ident("deref")))
                .collect();

            match marked.len() {
                0 => Err(syn::Error::new_spanned(
                    name,
                    "multiple fields require exactly one `#[deref]` attribute",
                )),
                1 => {
                    let (idx, field) = marked[0];
                    let ty = field.ty.clone();
                    let idx = syn::Index::from(idx);
                    let access = quote!(#idx);
                    Ok((ty, access))
                }
                _ => Err(syn::Error::new_spanned(
                    name,
                    "only one field may have `#[deref]`",
                )),
            }
        }
        Fields::Unit => Err(syn::Error::new_spanned(
            name,
            "Deref/DerefMut cannot be derived for unit structs",
        )),
    }
}

// =============================================================================
// #[derive(Param)]
// =============================================================================

/// Derive the `Param` trait for a struct, enabling it to be used as a
/// grouped handler parameter.
///
/// The struct must have exactly one lifetime parameter. Each field must
/// implement `Param`, or be annotated with `#[param(ignore)]` (in which
/// case it must implement `Default`).
///
/// ```ignore
/// use nexus_rt::{Param, Res, ResMut, Local};
///
/// #[derive(Param)]
/// struct TradingParams<'w> {
///     book: Res<'w, OrderBook>,
///     risk: ResMut<'w, RiskState>,
///     local_count: Local<'w, u64>,
/// }
///
/// fn on_order(params: TradingParams<'_>, order: Order) {
///     // params.book, params.risk, params.local_count all available
/// }
/// ```
#[proc_macro_derive(Param, attributes(param))]
pub fn derive_param(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_param_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_param_impl(input: &DeriveInput) -> Result<proc_macro2::TokenStream, syn::Error> {
    let name = &input.ident;

    // Validate: must be a struct
    let fields = match &input.data {
        Data::Struct(s) => &s.fields,
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "derive(Param) can only be applied to structs",
            ));
        }
    };

    // Validate: exactly one lifetime parameter, no type/const generics
    let lifetimes: Vec<_> = input.generics.lifetimes().collect();
    if lifetimes.len() != 1 {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "derive(Param) requires exactly one lifetime parameter, \
             e.g., `struct MyParam<'w>`",
        ));
    }
    // TODO: support type and const generics by threading them through
    // the generated State struct and Param impl (e.g., `Buffer<const N: usize>`).
    // This is straightforward with syn's split_for_impl() but deferred to
    // avoid the lifetime inference issues Bevy hit with generic SystemParams.
    if input.generics.type_params().next().is_some()
        || input.generics.const_params().next().is_some()
    {
        return Err(syn::Error::new_spanned(
            &input.generics,
            "derive(Param) does not yet support type or const generics — \
             only a single lifetime parameter (e.g., `struct MyParam<'w>`). \
             Use a concrete type instead (e.g., `Res<'w, Buffer<64>>` not `Res<'w, Buffer<N>>`)",
        ));
    }
    let world_lifetime = &lifetimes[0].lifetime;

    // Must be named fields
    let named_fields = match fields {
        Fields::Named(f) => &f.named,
        _ => {
            return Err(syn::Error::new_spanned(
                name,
                "derive(Param) requires named fields",
            ));
        }
    };

    // Classify fields: param fields (participate in init/fetch) vs ignored
    let mut param_fields = Vec::new();
    let mut ignored_fields = Vec::new();

    for field in named_fields {
        let field_name = field.ident.as_ref().unwrap();
        let is_ignored = field.attrs.iter().any(|a| {
            a.path().is_ident("param")
                && a.meta
                    .require_list()
                    .is_ok_and(|l| l.tokens.to_string().trim() == "ignore")
        });

        if is_ignored {
            ignored_fields.push(field_name);
        } else {
            // Substitute the struct's lifetime with 'static in the field type
            let mut static_ty = field.ty.clone();
            let mut replacer = LifetimeReplacer {
                from: world_lifetime.ident.to_string(),
            };
            replacer.visit_type_mut(&mut static_ty);

            param_fields.push((field_name, &field.ty, static_ty));
        }
    }

    // Generate the State struct name
    let state_name = format_ident!("{}State", name);

    // State struct fields
    let state_fields = param_fields.iter().map(|(field_name, _, static_ty)| {
        quote! {
            #field_name: <#static_ty as ::nexus_rt::Param>::State
        }
    });
    let ignored_state_fields = ignored_fields.iter().map(|field_name| {
        quote! {
            #field_name: ()
        }
    });

    // init() body
    let init_fields = param_fields.iter().map(|(field_name, _, static_ty)| {
        quote! {
            #field_name: <#static_ty as ::nexus_rt::Param>::init(registry)
        }
    });
    let init_ignored = ignored_fields.iter().map(|field_name| {
        quote! { #field_name: () }
    });

    // fetch() body
    let fetch_fields = param_fields.iter().map(|(field_name, _, static_ty)| {
        quote! {
            #field_name: <#static_ty as ::nexus_rt::Param>::fetch(world, &mut state.#field_name)
        }
    });
    let fetch_ignored = ignored_fields.iter().map(|field_name| {
        quote! {
            #field_name: ::core::default::Default::default()
        }
    });

    Ok(quote! {
        #[doc(hidden)]
        #[allow(non_camel_case_types)]
        pub struct #state_name {
            #(#state_fields,)*
            #(#ignored_state_fields,)*
        }

        impl ::nexus_rt::Param for #name<'_> {
            type State = #state_name;
            type Item<'w> = #name<'w>;

            fn init(registry: &::nexus_rt::Registry) -> Self::State {
                #state_name {
                    #(#init_fields,)*
                    #(#init_ignored,)*
                }
            }

            unsafe fn fetch<'w>(
                world: &'w ::nexus_rt::World,
                state: &'w mut Self::State,
            ) -> #name<'w> {
                #name {
                    #(#fetch_fields,)*
                    #(#fetch_ignored,)*
                }
            }
        }
    })
}

/// Replaces occurrences of a specific lifetime with `'static`.
struct LifetimeReplacer {
    from: String,
}

impl VisitMut for LifetimeReplacer {
    fn visit_lifetime_mut(&mut self, lt: &mut Lifetime) {
        if lt.ident == self.from {
            *lt = Lifetime::new("'static", lt.apostrophe);
        }
    }
}

// =============================================================================
// #[derive(View)]
// =============================================================================

/// Derive a `View` projection for use with pipeline `.view()` scopes.
///
/// Generates a marker ZST (`As{ViewName}`) and `unsafe impl View<Source>`
/// for each `#[source(Type)]` attribute. Use with `.view::<AsViewName>()`
/// in pipeline and DAG builders.
///
/// Type and const generic parameters are supported. Non-`#[borrow]` fields
/// with generic types must be `Copy` (they are copied from `&source`).
///
/// # Attributes
///
/// **On the struct:**
/// - `#[source(TypePath)]` — one per source event type
///
/// **On fields:**
/// - `#[borrow]` — borrow from source (`&source.field`) instead of copy
/// - `#[source(TypePath, from = "name")]` — remap field name for a specific source
///
/// # Examples
///
/// ```ignore
/// use nexus_rt::View;
///
/// #[derive(View)]
/// #[source(NewOrderCommand)]
/// #[source(AmendOrderCommand)]
/// struct OrderView<'a> {
///     #[borrow]
///     symbol: &'a str,
///     qty: u64,
///     price: f64,
/// }
///
/// // Generates: struct AsOrderView;
/// // Generates: unsafe impl View<NewOrderCommand> for AsOrderView { ... }
/// // Generates: unsafe impl View<AmendOrderCommand> for AsOrderView { ... }
/// ```
#[proc_macro_derive(View, attributes(source, borrow))]
pub fn derive_view(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match derive_view_impl(&input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn derive_view_impl(input: &DeriveInput) -> Result<proc_macro2::TokenStream, syn::Error> {
    // Only structs
    let fields = match &input.data {
        Data::Struct(s) => match &s.fields {
            Fields::Named(f) => &f.named,
            _ => {
                return Err(syn::Error::new_spanned(
                    &input.ident,
                    "#[derive(View)] only supports structs with named fields",
                ));
            }
        },
        _ => {
            return Err(syn::Error::new_spanned(
                &input.ident,
                "#[derive(View)] can only be used on structs",
            ));
        }
    };

    let view_name = &input.ident;
    let vis = &input.vis;

    // Extract #[source(TypePath)] attributes from the struct
    let sources = parse_source_attrs(&input.attrs, view_name)?;
    if sources.is_empty() {
        return Err(syn::Error::new_spanned(
            view_name,
            "#[derive(View)] requires at least one #[source(Type)] attribute",
        ));
    }

    // Detect lifetime: 0 or 1 lifetime param
    let lifetime_param = match input.generics.lifetimes().count() {
        0 => None,
        1 => Some(input.generics.lifetimes().next().unwrap().lifetime.clone()),
        _ => {
            return Err(syn::Error::new_spanned(
                &input.generics,
                "#[derive(View)] supports at most one lifetime parameter",
            ));
        }
    };

    // Marker name: As{ViewName}
    let marker_name = format_ident!("As{}", view_name);

    // Build marker generics (type + const params only, no lifetimes)
    let mut marker_generics = input.generics.clone();
    marker_generics.params = marker_generics
        .params
        .into_iter()
        .filter(|p| !matches!(p, GenericParam::Lifetime(_)))
        .collect();
    // Strip lifetime bounds from type params (e.g., T: 'a + Copy → T: Copy)
    for param in &mut marker_generics.params {
        if let GenericParam::Type(tp) = param {
            tp.bounds = tp
                .bounds
                .iter()
                .filter(|b| !matches!(b, TypeParamBound::Lifetime(_)))
                .cloned()
                .collect();
        }
    }
    // Strip where-clause predicates referencing the view lifetime
    if let Some(lt) = &lifetime_param
        && let Some(where_clause) = &mut marker_generics.where_clause
    {
        let lt_ident = lt.ident.to_string();
        where_clause.predicates = where_clause
            .predicates
            .iter()
            .filter(|pred| {
                let tokens = quote! { #pred }.to_string();
                !tokens.contains(&lt_ident)
            })
            .cloned()
            .collect();
    }
    // View::StaticViewType: 'static requires all type params to be 'static
    {
        let where_clause = marker_generics.make_where_clause();
        for tp in input.generics.type_params() {
            let ident = &tp.ident;
            where_clause
                .predicates
                .push(syn::parse_quote!(#ident: 'static));
        }
    }
    let (marker_impl_generics, marker_ty_generics, marker_where) = marker_generics.split_for_impl();

    // PhantomData fields for type params (const params don't need phantom data)
    let phantom_fields: Vec<proc_macro2::TokenStream> = input
        .generics
        .type_params()
        .map(|tp| {
            let ident = &tp.ident;
            quote! { ::core::marker::PhantomData<fn() -> #ident> }
        })
        .collect();

    // Non-lifetime param idents for use in type position (no bounds)
    let non_lt_params: Vec<proc_macro2::TokenStream> = input
        .generics
        .params
        .iter()
        .filter_map(|p| match p {
            GenericParam::Type(tp) => {
                let ident = &tp.ident;
                Some(quote! { #ident })
            }
            GenericParam::Const(cp) => {
                let ident = &cp.ident;
                Some(quote! { #ident })
            }
            GenericParam::Lifetime(_) => None,
        })
        .collect();

    // Build ViewType<'a>, StaticViewType, and tick-lifetime tokens
    let has_non_lt = !non_lt_params.is_empty();
    let (view_type_with_a, static_view_type, view_type_tick) = match (&lifetime_param, has_non_lt) {
        (Some(_), true) => (
            quote! { #view_name<'a, #(#non_lt_params),*> },
            quote! { #view_name<'static, #(#non_lt_params),*> },
            quote! { #view_name<'_, #(#non_lt_params),*> },
        ),
        (Some(_), false) => (
            quote! { #view_name<'a> },
            quote! { #view_name<'static> },
            quote! { #view_name<'_> },
        ),
        (None, true) => (
            quote! { #view_name<#(#non_lt_params),*> },
            quote! { #view_name<#(#non_lt_params),*> },
            quote! { #view_name<#(#non_lt_params),*> },
        ),
        (None, false) => (
            quote! { #view_name },
            quote! { #view_name },
            quote! { #view_name },
        ),
    };

    // Parse field info
    let field_infos: Vec<FieldInfo> = fields
        .iter()
        .map(parse_field_info)
        .collect::<Result<_, _>>()?;

    // Generate impl for each source
    let mut impls = Vec::new();
    for source_type in &sources {
        let field_exprs: Vec<proc_macro2::TokenStream> = field_infos
            .iter()
            .map(|fi| {
                let view_field = &fi.ident;
                // Check for per-source field remap
                let source_field = fi
                    .remaps
                    .iter()
                    .find(|(path, _)| path_matches(path, source_type))
                    .map_or_else(|| fi.ident.clone(), |(_, name)| format_ident!("{}", name));

                if fi.borrow {
                    quote! { #view_field: &source.#source_field }
                } else {
                    quote! { #view_field: source.#source_field }
                }
            })
            .collect();

        impls.push(quote! {
            // SAFETY: ViewType<'a> and StaticViewType are the same struct
            // with different lifetime parameters. Layout-identical by construction.
            unsafe impl #marker_impl_generics ::nexus_rt::View<#source_type>
                for #marker_name #marker_ty_generics
                #marker_where
            {
                type ViewType<'a> = #view_type_with_a where #source_type: 'a;
                type StaticViewType = #static_view_type;

                fn view(source: &#source_type) -> #view_type_tick {
                    #view_name {
                        #(#field_exprs),*
                    }
                }
            }
        });
    }

    let marker_struct = if phantom_fields.is_empty() {
        quote! {
            /// View marker generated by `#[derive(View)]`.
            #vis struct #marker_name #marker_impl_generics #marker_where;
        }
    } else {
        quote! {
            /// View marker generated by `#[derive(View)]`.
            #vis struct #marker_name #marker_impl_generics (
                #(#phantom_fields),*
            ) #marker_where;
        }
    };

    Ok(quote! {
        #marker_struct

        #(#impls)*
    })
}

struct FieldInfo {
    ident: syn::Ident,
    borrow: bool,
    /// Per-source field remaps: (source_path, source_field_name)
    remaps: Vec<(syn::Path, String)>,
}

fn parse_field_info(field: &syn::Field) -> Result<FieldInfo, syn::Error> {
    let ident = field
        .ident
        .clone()
        .ok_or_else(|| syn::Error::new_spanned(field, "View fields must be named"))?;

    let borrow = field.attrs.iter().any(|a| a.path().is_ident("borrow"));

    let mut remaps = Vec::new();
    for attr in &field.attrs {
        if attr.path().is_ident("source") {
            // Parse #[source(TypePath, from = "field_name")]
            attr.parse_args_with(|input: syn::parse::ParseStream| {
                let path: syn::Path = input.parse()?;

                if input.is_empty() {
                    return Ok(());
                }

                input.parse::<syn::Token![,]>()?;
                let kw: syn::Ident = input.parse()?;
                if kw != "from" {
                    return Err(syn::Error::new_spanned(&kw, "expected `from`"));
                }
                input.parse::<syn::Token![=]>()?;
                let lit: syn::LitStr = input.parse()?;
                remaps.push((path, lit.value()));
                Ok(())
            })?;
        }
    }

    Ok(FieldInfo {
        ident,
        borrow,
        remaps,
    })
}

/// Parse `#[source(TypePath)]` attributes from struct-level attrs.
fn parse_source_attrs(
    attrs: &[syn::Attribute],
    span_target: &syn::Ident,
) -> Result<Vec<syn::Path>, syn::Error> {
    let mut sources = Vec::new();
    for attr in attrs {
        if attr.path().is_ident("source") {
            let path: syn::Path = attr.parse_args()?;
            sources.push(path);
        }
    }
    let _ = span_target; // used for error span if needed
    Ok(sources)
}

/// Check if two paths match by comparing full path equality.
fn path_matches(a: &syn::Path, b: &syn::Path) -> bool {
    a == b
}

// =============================================================================
// select! — compile-time dispatch table
// =============================================================================

/// Compile-time dispatch table for pipeline/DAG steps — the nexus-rt
/// analogue of tokio's `select!`.
///
/// Eliminates the `resolve_step` + match-closure boilerplate by expanding
/// to a literal `match` with pre-resolved monomorphized arms. Preserves
/// exhaustiveness checking, jump table optimization, and zero-cost
/// monomorphization.
///
/// # Grammar
///
/// ```text
/// select! {
///     <reg>,
///     [ctx: <Type>,]          // callback mode (optional)
///     [key: <closure>,]       // key extraction (optional)
///     [project: <closure>,]   // input projection (optional, requires key:)
///     <pattern> => <handler>,
///     ...
///     [_ => <default>,]       // fallthrough (optional, must be last)
/// }
/// ```
///
/// Or-patterns, literal patterns, and any other pattern rustc accepts
/// work because the expansion is a real `match`.
///
/// # Three tiers of ceremony
///
/// **Tier 1** — input is the match value, arms take the input. No
/// `key:`, no `project:`. Use when upstream has already classified
/// the event down to a discriminant.
///
/// ```ignore
/// select! {
///     reg,
///     OrderKind::New    => handle_new,
///     OrderKind::Cancel => handle_cancel,
/// }
/// ```
///
/// **Tier 2** — input is a struct, match on a field, arms take the
/// whole struct. The most common shape.
///
/// ```ignore
/// select! {
///     reg,
///     key: |o: &Order| o.kind,
///     OrderKind::New    => handle_new,
///     OrderKind::Cancel => handle_cancel,
/// }
/// ```
///
/// **Tier 3** — input is a composite (e.g., a tuple), arms take a
/// projection. Use when upstream emits both a discriminant and a
/// payload side-by-side.
///
/// ```ignore
/// select! {
///     reg,
///     key:     |(_, ct): &(Event, CmdType)| *ct,
///     project: |(e, _)| e,
///     CmdType::A => handle_a,
///     CmdType::B => handle_b,
///     _ => |_w, (e, ct)| log::error!("unsupported {:?} id={}", ct, e.id),
/// }
/// ```
///
/// # Callback form (with `ctx:`)
///
/// Adding `ctx: SomeContext` switches the expansion from
/// `resolve_step` to `resolve_ctx_step` and threads `&mut SomeContext`
/// through every arm. Works with `CtxPipelineBuilder` and
/// `CtxDagBuilder`. All three tiers apply.
///
/// ```ignore
/// select! {
///     reg,
///     ctx: SessionCtx,
///     key: |o: &Order| o.kind,
///     OrderKind::New    => on_new,    // fn(&mut SessionCtx, Order)
///     OrderKind::Cancel => on_cancel,
/// }
/// ```
///
/// # `key:` closures need a type annotation
///
/// When `key:` is present, the closure parameter must have an explicit
/// type annotation (e.g., `|o: &Order| o.kind`). Without it, rustc
/// can't infer the input type at the point of key extraction. This is
/// a fundamental Rust closure-inference limitation, not a macro issue.
///
/// `project:` closures do **not** need annotation — they're called
/// inside match arms after `key:` has already constrained the input
/// type.
///
/// # Performance
///
/// Zero overhead. The expansion is identical to the hand-written
/// `let mut arm_N = resolve_step(...)` + closure + match pattern.
/// `cargo asm` on `examples/select_asm_check.rs` confirms the
/// dispatch compiles to a jump table for dense enum discriminants.
///
/// See `nexus-rt/docs/pipelines.md` and `nexus-rt/docs/callbacks.md`
/// for full usage guides.
#[proc_macro]
pub fn select(input: TokenStream) -> TokenStream {
    let parsed = parse_macro_input!(input as select::SelectInput);
    select::expand(&parsed).into()
}
