extern crate proc_macro;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{self, Parse, ParseStream};
use syn::{self, DeriveInput, Token};
use synstructure::{AddBounds, Structure};

/// Derives neutralizing traits.
///
/// For now, there is only one syntax accepted by this macro attribute.
///
/// ### `#[inert::neutralize(as Self)]`
///
/// Implements `NeutralizeUnsafe` with `type Output = Self;`. Given that this
/// can type check if and only if `Self` is `Sync`, the traits `Neutralize`
/// and `NeutralizeMut` are also automatically implemented.
#[proc_macro_attribute]
pub fn neutralize(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut result = item.clone();

    let attr = syn::parse_macro_input!(attr as NeutralizeAttr);
    let input = syn::parse_macro_input!(item as DeriveInput);
    let mut structure = Structure::new(&input);

    structure.add_bounds(AddBounds::None);

    #[allow(non_snake_case)]
    match attr {
        NeutralizeAttr::AsSelf(Self_) => {
            // https://github.com/mystor/synstructure/issues/25
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                extern crate inert;

                gen unsafe impl ::inert::Neutralize for @Self {}
            })));
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                extern crate inert;

                gen unsafe impl ::inert::NeutralizeMut for @Self {}
            })));
            result.extend(TokenStream::from(structure.gen_impl(quote! {
                extern crate inert;

                gen unsafe impl ::inert::NeutralizeUnsafe for @Self {
                    type Output = #Self_;

                    unsafe fn neutralize_unsafe(&self) -> &Self::Output { self }
                }
            })));
        },
    };

    result
}

enum NeutralizeAttr {
    AsSelf(Token![Self]),
}

impl Parse for NeutralizeAttr {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        input.parse::<Token![as]>()?;
        input.parse().map(NeutralizeAttr::AsSelf)
    }
}
