use super::*;

#[derive(Default)]
pub(crate) struct Errors {
    pub(crate) errors: Vec<syn::Error>,
}

impl Errors {
    pub(crate) fn push(&mut self, e: syn::Error) {
        self.errors.push(e);
    }

    pub(crate) fn into_result(self) -> Result<(), syn::Error> {
        let mut iter = self.errors.into_iter();
        if let Some(mut errors) = iter.next() {
            for e in iter {
                errors.combine(e);
            }
            Err(errors)
        } else {
            Ok(())
        }
    }

    pub(crate) fn into_token_stream(self) -> TokenStream {
        if self.errors.is_empty() {
            return TokenStream::new();
        }

        let mut t = TokenStream::new();
        for e in self.errors.into_iter() {
            t.extend(e.into_compile_error().into_token_stream());
        }
        t
    }

    pub(crate) fn into_token_stream_and_combine(self, mut t: TokenStream) -> TokenStream {
        if self.errors.is_empty() {
            return t;
        }
        t.extend(self.into_token_stream());
        t
    }

    #[allow(dead_code)]
    pub(crate) fn with_value<T>(self, value: T) -> WithErrors<T> {
        WithErrors {
            errors: self,
            value,
        }
    }


    #[allow(dead_code)]
    pub(crate) fn combine_with<T>(&mut self, mut with: WithErrors<T>) -> T {
        self.errors.append(&mut with.errors.errors);
        with.value
    }
}

/// Represents a value and a list of errors (potentially empty).
pub(crate) struct WithErrors<T> {
    errors: Errors,
    value: T,
}
