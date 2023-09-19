//! Contains the supporting logic needed for applications that wish to use RACC-generated parsers.
//! There used to be more stuff in `racc_runtime`, but now there is only a single `Error` type.
//! Even this might be eliminated and folded into the generated code.

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    SyntaxError,
    /// This is a terrible way to handle app errors.
    /// TODO: Find some better way.
    AppError,
}

#[cfg(feature = "racc_log")]
#[macro_export]
macro_rules! racc_log {
    (
        $($t:tt)*
    ) => {
        ::log::debug!( $($t)* )
    }
}

#[cfg(not(feature = "racc_log"))]
#[macro_export]
macro_rules! racc_log {
    (
        $($t:tt)*
    ) => {
        // nothing
    };
}
