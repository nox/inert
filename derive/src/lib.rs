extern crate proc_macro;

use proc_macro2::TokenStream;
use quote::{quote, quote_spanned};
use syn::parse::{Error, Parse, ParseStream};
use syn::spanned::Spanned;
use syn::token::{Brace, Bracket, Paren};
use syn::{
    self, Attribute, Data, DeriveInput, Field, Fields, GenericParam, Ident, Path, Token, Visibility,
};

/// Derives neutralizing traits.
///
/// There are two ways to use this procedural macro attribute.
///
/// ### `#[inert::neutralize(as Self)]`
///
/// Implements `NeutralizeUnsafe` with `type Output = Self;`. Given that this
/// can type check if and only if `Self` is `Sync`, the traits `Neutralize`
/// and `NeutralizeMut` are also automatically implemented.
///
/// ### `#[inert::neutralize(as vis? unsafe InertFoo)]`
///
/// Implements `NeutralizeUnsafe` with `type Output = InertFoo;`. `InertFoo` is
/// a wrapper generated by the macro itself, its visibility is controlled
/// by `vis`. A getter method named is generated for each field adorned with
/// `#[inert::field(vis? ident?)]`, if `ident` is missing, the getter is given
/// the same name as the field itself.
///
/// Given the following `Node` type:
///
/// ```ignore
/// #[inert::neutralize(as pub(crate) unsafe InertNode)]
/// struct Node {
///     #[inert::field(pub(crate) tag)]
///     name: String,
///     #[inert::field(pub(crate))]
///     attributes: Vec<Attribute>,
///     #[inert::field]
///     children: RefCell<Vec<Node>>,
/// }
/// ```
///
/// The following code will be generated:
///
/// ```ignore
/// pub(crate) struct InertNode {
///     value: inert::Neutralized<Node>,
/// }
///
/// unsafe impl NeutralizeUnsafe for Node {
///     type Output = InertNode;
///
///     unsafe fn neutralize_unsafe(&self) -> &InertNode {
///         &*(self as *const Self as *const Self::Output)
///     }
/// }
///
/// impl InertNode {
///     pub(crate) fn tag(&self) -> &Inert<String> {
///         unsafe { Inert::new_unchecked(&self.name) }
///     }
///
///     pub(crate) fn attributes(&self) -> &Inert<Vec<Attribute>> {
///         unsafe { Inert::new_unchecked(&self.attributes) }
///     }
///
///     fn children(&self) -> &Inert<RefCell<Vec<Node>>> {
///         unsafe { Inert::new_unchecked(&self.children) }
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn neutralize(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr = syn::parse_macro_input!(attr as NeutralizeAttr);
    let input = syn::parse_macro_input!(item as DeriveInput);
    match attr {
        NeutralizeAttr::AsSelf(self_type) => neutralize_as_self(self_type, input),
        NeutralizeAttr::AsWrapper(wrapper) => {
            neutralize_as_wrapper(wrapper, input).unwrap_or_else(|e| e.to_compile_error().into())
        },
    }.into()
}

enum NeutralizeAttr {
    AsSelf(Token![Self]),
    AsWrapper(Wrapper),
}

impl Parse for NeutralizeAttr {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        input.parse::<Token![as]>()?;
        if input.peek(Token![Self]) {
            return input.parse::<Token![Self]>().map(NeutralizeAttr::AsSelf);
        }
        input.parse().map(NeutralizeAttr::AsWrapper)
    }
}

struct Wrapper {
    vis: Visibility,
    name: Ident,
}

impl Parse for Wrapper {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let vis = input.parse()?;
        input.parse::<Token![unsafe]>()?;
        let name = input.parse()?;
        Ok(Self { vis, name })
    }
}

// FIXME(nox): https://github.com/dtolnay/syn/issues/589
struct AttrArgument<T> {
    argument: T,
}

// FIXME(nox): https://github.com/dtolnay/syn/issues/589
impl<T> Parse for AttrArgument<T>
where
    T: Parse,
{
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let content;
        if input.peek(Paren) {
            syn::parenthesized!(content in input);
        } else if input.peek(Brace) {
            syn::braced!(content in input);
        } else if input.peek(Bracket) {
            syn::bracketed!(content in input);
        } else {
            return Ok(Self { argument: syn::parse2(quote! {})? });
        }
        let argument = T::parse(&content)?;
        Ok(Self { argument })
    }
}

struct FieldAttr {
    vis: Visibility,
    name: Option<Ident>,
}

impl Parse for FieldAttr {
    fn parse(input: ParseStream) -> Result<Self, Error> {
        let vis = input.parse()?;
        let name = input.parse()?;
        Ok(Self { vis, name })
    }
}

fn neutralize_as_self(self_type: Token![Self], input: DeriveInput) -> TokenStream {
    let type_name = &input.ident;
    let (impl_gen, ty_gen, where_) = input.generics.split_for_impl();

    // This is supposed to improve "trait bound is not satisfied" errors
    // in case Self is !Sync, but this does not actually work yet.
    //
    // https://github.com/rust-lang/rust/issues/41817
    let output = quote_spanned! {self_type.span()=> type Output = Self; };

    quote! {
        #input

        unsafe impl #impl_gen ::inert::Neutralize for #type_name #ty_gen #where_ {}
        unsafe impl #impl_gen ::inert::NeutralizeMut for #type_name #ty_gen #where_ {}

        unsafe impl #impl_gen ::inert::NeutralizeUnsafe for #type_name #ty_gen #where_ {
            #output

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &Self { self }
        }
    }
}

fn neutralize_as_wrapper(wrapper: Wrapper, mut input: DeriveInput) -> Result<TokenStream, Error> {
    check_params(&input)?;

    let methods = inert_methods(struct_fields_mut(&mut input)?)?;

    let Wrapper { vis, name } = wrapper;
    let type_name = &input.ident;
    let (impl_gen, ty_gen, where_) = input.generics.split_for_impl();

    let wrapper = quote_spanned! {name.span()=>
        #vis struct #name #ty_gen #where_ {
            #[allow(dead_code)]
            value: ::inert::Neutralized<#type_name #ty_gen>,
        }
    };

    Ok(quote! {
        #input

        #wrapper

        unsafe impl #impl_gen ::inert::NeutralizeUnsafe for #type_name #ty_gen #where_ {
            type Output = #name #ty_gen;

            #[inline]
            unsafe fn neutralize_unsafe(&self) -> &#name #ty_gen {
                &*(self as *const Self as *const Self::Output)
            }
        }

        impl #impl_gen #name #ty_gen #where_ {
            #methods
        }
    })
}

fn check_params(input: &DeriveInput) -> Result<(), Error> {
    for param in &input.generics.params {
        if let GenericParam::Lifetime(_) = *param {
            continue;
        }
        return Err(Error::new(
            param.span(),
            "cannot automatically neutralize a parameterized type",
        ));
    }
    Ok(())
}

fn struct_fields_mut(input: &mut DeriveInput) -> Result<impl Iterator<Item = &mut Field>, Error> {
    // FIXME(nox): https://github.com/rust-lang/rust/issues/58910
    let span = input.span();
    if let Data::Struct(ref mut data_struct) = input.data {
        if let Fields::Named(ref mut fields_named) = data_struct.fields {
            return Ok(fields_named.named.iter_mut());
        }
    }
    Err(Error::new(span, "only structs can be automatically neutralized"))
}

#[allow(dead_code)]
fn inert_methods<'input>(
    fields: impl Iterator<Item = &'input mut Field>,
) -> Result<TokenStream, Error> {
    let mut methods = quote! {};

    for field in fields {
        let attr = match extract_inert_field(field)? {
            Some(attr) => attr,
            None => continue,
        };

        let field_name = field.ident.as_ref().expect("named field");
        let ty = &field.ty;
        let FieldAttr { vis, name } = attr;
        let getter_name = name.as_ref().unwrap_or(field_name);

        methods.extend(quote_spanned! {field.ty.span()=>
            #[allow(unsafe_code)]
            #[inline]
            #vis fn #getter_name(&self) -> &inert::Inert<#ty> {
                unsafe { inert::Inert::new_unchecked(&self.value.as_ref().#field_name) }
            }
        });
    }

    Ok(methods)
}

fn extract_inert_field(field: &mut Field) -> Result<Option<FieldAttr>, Error> {
    let (pos, attr) = if let Some(pos) = find_inert_field_attr(&field.attrs) {
        (pos, field.attrs.remove(pos))
    } else {
        return Ok(None);
    };

    let attr = syn::parse2::<AttrArgument<FieldAttr>>(attr.tts)?.argument;

    if let Some(dupe_pos) = find_inert_field_attr(&field.attrs[pos..]) {
        return Err(Error::new(
            field.attrs[pos..][dupe_pos].span(),
            "multiple #[inert::field] attributes found on the same field",
        ));
    }

    Ok(Some(attr))
}

fn find_inert_field_attr<'input>(
    attrs: impl IntoIterator<Item = &'input Attribute>,
) -> Option<usize> {
    attrs.into_iter().position(|attr| is_simple_path(&attr.path, &["inert", "field"]))
}

fn is_simple_path(path: &Path, idents: &[&str]) -> bool {
    let mut segments = path.segments.iter();
    let mut idents = idents.iter();
    segments.by_ref().zip(idents.by_ref()).all(|(s, i)| s.ident == *i && s.arguments.is_empty())
        && segments.next().is_none()
        && idents.next().is_none()
}
