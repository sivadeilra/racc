/// Contains the supporting logic needed for applications that wish to use RACC-generated parsers.

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    SyntaxError,
    /// This is a terrible way to handle app errors.
    /// TODO: Find some better way.
    AppError,
}
