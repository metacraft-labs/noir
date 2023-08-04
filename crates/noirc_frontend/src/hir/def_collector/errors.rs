use crate::hir::resolution::import::PathResolutionError;
use crate::Ident;

use noirc_errors::CustomDiagnostic as Diagnostic;
use noirc_errors::FileDiagnostic;
use noirc_errors::Span;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DefCollectorErrorKind {
    #[error("duplicate {typ} found in namespace")]
    Duplicate { typ: String, first_def: Ident, second_def: Ident },
    #[error("unresolved import")]
    UnresolvedModuleDecl { mod_name: Ident },
    #[error("path resolution error")]
    PathResolutionError(PathResolutionError),
    #[error("Non-struct type used in impl")]
    NonStructTypeInImpl { span: Span },
    #[error("Generic error")]
    GenericError { primary_message: String, secondary_message: String, span: Span },
}

impl DefCollectorErrorKind {
    pub fn into_file_diagnostic(self, file: fm::FileId) -> FileDiagnostic {
        Diagnostic::from(self).in_file(file)
    }
}

impl From<DefCollectorErrorKind> for Diagnostic {
    fn from(error: DefCollectorErrorKind) -> Diagnostic {
        match error {
            DefCollectorErrorKind::Duplicate { typ, first_def, second_def } => {
                let primary_message =
                    format!("duplicate definitions of {} function found", &first_def.0.contents);
                {
                    let duplicate_type: &str = &typ;
                    let first_span = first_def.0.span();
                    let second_span = second_def.0.span();
                    let mut diag = Diagnostic::simple_error(
                        primary_message,
                        format!("first {} found here", duplicate_type),
                        first_span,
                    );
                    diag.add_secondary(
                        format!("second {} found here", duplicate_type),
                        second_span,
                    );
                    diag
                }
            }
            DefCollectorErrorKind::UnresolvedModuleDecl { mod_name } => {
                let span = mod_name.0.span();
                let mod_name = &mod_name.0.contents;

                Diagnostic::simple_error(
                    format!("could not resolve module `{mod_name}` "),
                    String::new(),
                    span,
                )
            }
            DefCollectorErrorKind::PathResolutionError(error) => error.into(),
            DefCollectorErrorKind::NonStructTypeInImpl { span } => Diagnostic::simple_error(
                "Non-struct type used in impl".into(),
                "Only struct types may have implementation methods".into(),
                span,
            ),
            DefCollectorErrorKind::GenericError { primary_message, secondary_message, span } => {
                Diagnostic::simple_error(primary_message, secondary_message, span)
            }
        }
    }
}
