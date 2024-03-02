use itertools::Itertools as _;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, DeriveInput, LitStr, Meta, MetaList, Token,
};

#[proc_macro_derive(new, attributes(oleclient))]
pub fn derive_new(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    return derive_new(input)
        .map(Into::into)
        .unwrap_or_else(|e| e.to_compile_error().into());

    fn derive_new(input: DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
        let DeriveInput {
            attrs, vis, ident, ..
        } = &input;

        let AttrVal(prog_id) = attrs
            .iter()
            .flat_map(|attr| match &attr.meta {
                Meta::List(MetaList { path, .. }) if path.is_ident("oleclient") => {
                    Some(attr.parse_args::<AttrVal>())
                }
                _ => None,
            })
            .exactly_one()
            .map_err(|_| {
                syn::Error::new(proc_macro2::Span::call_site(), "missing `#[oleclient(…)]`")
            })??;

        let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

        Ok(quote! {
            impl #impl_generics #ident #ty_generics #where_clause {
                #vis fn new() -> ::oleclient::Result<Self> {
                    let disp = ::oleclient::idispatch_from_prog_id(::windows::core::w!(#prog_id))?;
                    Ok(::std::convert::From::from(disp))
                }
            }
        })
    }

    struct AttrVal(LitStr);

    impl Parse for AttrVal {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let key = input.parse::<syn::Ident>()?;
            if key != "prog_id" {
                return Err(syn::Error::new(key.span(), "expected `\"prog_id\"`"));
            }
            input.parse::<Token![=]>()?;
            let val = input.parse::<LitStr>()?;
            if !input.is_empty() {
                return Err(syn::Error::new(input.span(), "expected end"));
            }
            Ok(Self(val))
        }
    }
}

#[proc_macro_derive(TryFrom_Out)]
pub fn derive_try_from_out(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    return derive_try_from_out(input)
        .map(Into::into)
        .unwrap_or_else(|e| e.to_compile_error().into());

    fn derive_try_from_out(input: DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
        let DeriveInput { ident, .. } = &input;

        let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

        Ok(quote! {
            impl #impl_generics ::std::convert::TryFrom<::oleclient::Out> for #ident #ty_generics
            #where_clause
            {
                type Error = ::oleclient::Error;

                fn try_from(out: ::oleclient::Out) -> ::oleclient::Result<Self> {
                    let disp = out.into_idispatch()?;
                    Ok(Self::from(disp))
                }
            }
        })
    }
}
