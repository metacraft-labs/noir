use acvm::FieldElement;
use noirc_printable_type::{PrintableType, PrintableValue};

/// A stack frame during execution of the program being traced.
#[derive(Clone, Debug)]
pub(crate) struct StackFrame {
    pub(crate) function_name: String,
    /// The param indexes are used to address the `variables` vector; they indicate which of the
    /// variables in the stack frame are parameters.
    pub(crate) function_param_indexes: Vec<usize>,
    /// How many of the function's declared parameters the instrumenter binds under the name the
    /// frame declares, bound yet or not.
    ///
    /// `function_param_indexes` lists only the parameters that already have a value in
    /// `variables`, and under column-aware stepping a frame appears before any of its parameters
    /// is bound: the instrumenter binds them one step per parameter, at each parameter's own
    /// column in the signature. Comparing the two lengths is what tells the recorder whether a
    /// call record written now would carry every argument it will ever have; see
    /// [`StackFrame::all_params_bound`].
    ///
    /// A `_` or destructuring parameter is not counted: it is never bound under its declared
    /// name (see `debugger_glue::is_bindable_param_name`), so counting it would make the recorder
    /// wait for it until the function returns, and then record the parameters' values at the
    /// return instead of at the call.
    pub(crate) bindable_param_count: usize,
    /// A sorted vector of the frame variables. Not enforced, so beware of bugs.
    pub(crate) variables: Vec<Variable>,
}

impl StackFrame {
    /// Whether every parameter the instrumenter binds has a value in this frame.
    ///
    /// Always true for a function that declares no parameter, or only `_` and destructuring
    /// ones.
    pub(crate) fn all_params_bound(&self) -> bool {
        self.function_param_indexes.len() == self.bindable_param_count
    }
}

// Implement PartialEq for StackFrame manually, because it only needs to use the function_name as an
// identifier of the StackFrame. Considered using the derivative crate, but decided against it to
// keep dependency complexity low.
impl PartialEq for StackFrame {
    fn eq(&self, other: &Self) -> bool {
        self.function_name == other.function_name
    }
}

/// A representation of a variable on the stack. This representation owns the data that makes up the
/// variable -- the name, type, and value of the variable -- unlike the representation used by the
/// debugger.
#[derive(Clone, Debug)]
pub(crate) struct Variable {
    pub(crate) name: String,
    pub(crate) value: PrintableValue<FieldElement>,
    pub(crate) typ: PrintableType,
}

// The following trait implementations are added so that a collection of `Variable`s can be sorted
// using `.sort()`.
impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        self.name.eq(&other.name)
    }
}

impl Eq for Variable {
    fn assert_receiver_is_total_eq(&self) {
        self.name.assert_receiver_is_total_eq()
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.name.cmp(&other.name)
    }
}

impl Variable {
    /// Creates an instance from a tuple to references of the contents. Clones the variables
    /// pointed to by the references.
    ///
    /// It has this rather odd form and not a proper argument list, because this is the standard way
    /// variables are represented in the nargo debugger.
    pub(crate) fn from_tuple(
        args: &(&str, &PrintableValue<FieldElement>, &PrintableType),
    ) -> Variable {
        Variable { name: String::from(args.0), value: args.1.clone(), typ: args.2.clone() }
    }
}
