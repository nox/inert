extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{self, Parse, ParseStream};
use syn::{self, DeriveInput, Ident, Token, Visibility};
use synstructure::{AddBounds, Structure};

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
/// by `vis`.
///
/// Given the following `Foo` type:
///
/// ```ignore
/// #[inert::neutralize(as pub(crate) unsafe InertFoo)]
/// struct Foo(...);
/// ```
///
/// The following `InertFoo` wrapper will be generated:
///
/// ```ignore
/// pub(crate) struct InertFoo {
///     value: inert::Neutralized<Foo>,
/// }
/// ```
#[proc_macro_attribute]
pub fn neutralize(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut result = item.clone();

    let attr = syn::parse_macro_input!(attr as NeutralizeAttr);
    let input = syn::parse_macro_input!(item as DeriveInput);
    let mut structure = Structure::new(&input);

    structure.add_bounds(AddBounds::None);

    match attr {
        NeutralizeAttr::AsSelf(self_type) => {
            // https://github.com/mystor/synstructure/issues/25
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                gen unsafe impl ::inert::Neutralize for @Self {}
            })));
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                gen unsafe impl ::inert::NeutralizeMut for @Self {}
            })));
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                gen unsafe impl ::inert::NeutralizeUnsafe for @Self {
                    type Output = #self_type;

                    #[inline]
                    unsafe fn neutralize_unsafe(&self) -> &Self::Output { self }
                }
            })));
        },
        NeutralizeAttr::AsWrapper(Wrapper { vis, name: wrapper_name }) => {
            let name = &structure.ast().ident;
            let (_impl_generics, type_generics, where_clause) =
                structure.ast().generics.split_for_impl();
            result.extend(TokenStream::from(quote! {
                #vis struct #wrapper_name #type_generics #where_clause {
                    value: inert::Neutralized<#name #type_generics>,
                }
            }));
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                gen unsafe impl ::inert::NeutralizeUnsafe for @Self {
                    type Output = #wrapper_name #type_generics;

                    #[inline]
                    unsafe fn neutralize_unsafe(&self) -> &Self::Output {
                        &*(self as *const Self as *const Self::Output)
                    }
                }
            })))
        },
    };

    result
}

enum NeutralizeAttr {
    AsSelf(Token![Self]),
    AsWrapper(Wrapper),
}

struct Wrapper {
    vis: Visibility,
    name: Ident,
}

impl Parse for NeutralizeAttr {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<Token![as]>()?;
        if input.peek(Token![Self]) {
            return input.parse().map(NeutralizeAttr::AsSelf);
        }
        input.parse().map(NeutralizeAttr::AsWrapper)
    }
}

impl Parse for Wrapper {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        let vis = input.parse()?;
        input.parse::<Token![unsafe]>()?;
        let name = input.parse()?;
        Ok(Self { vis, name })
    }
}
