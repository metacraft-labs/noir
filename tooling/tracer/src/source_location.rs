use fm::PathString;
use std::path::PathBuf;

/// A location in the source code: filename, 1-indexed line number, and
/// an optional 1-indexed column number.
///
/// `column_number` is `None` for synthetic locations (compiler-generated
/// code, missing debug info) and for the "unknown" sentinel; otherwise
/// the recorder forwards it to the writer via
/// `register_step_with_column` so the replay can distinguish multiple
/// statements that share a source line.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SourceLocation {
    pub(crate) filepath: PathString,
    pub(crate) line_number: isize,
    pub(crate) column_number: Option<isize>,
}

impl SourceLocation {
    /// Creates a source location that represents an unknown place in the source code.
    pub(crate) fn create_unknown() -> SourceLocation {
        SourceLocation {
            filepath: PathString::from_path(PathBuf::from("?")),
            line_number: -1,
            column_number: None,
        }
    }
}
