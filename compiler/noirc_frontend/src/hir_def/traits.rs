use std::rc::Rc;

use crate::{
    node_interner::{FuncId, TraitId},
    Generics, Ident, Type, TypeBinding, TypeVariable, TypeVariableId,
};
use noirc_errors::Span;

#[derive(Debug, PartialEq, Eq)]
pub struct TraitFunction {
    pub name: Ident,
    pub generics: Generics, // TODO(vitkov): this not worky, need implement
    pub parameters: Vec<Type>,
    pub return_type: Type,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitConstant {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TraitType {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug)]
pub struct TraitGeneric {
    pub name: Rc<String>,
    pub typevar_id: TypeVariableId,
    pub typevar: TypeVariable,
    pub span: Span,
}

/// Represents a trait in the type system. Each instance of this struct
/// will be shared across all Type::Trait variants that represent
/// the same trait.
#[derive(Debug)]
pub struct Trait {
    /// A unique id representing this trait type. Used to check if two
    /// struct traits are equal.
    pub id: TraitId,

    pub methods: Vec<TraitFunction>,
    pub constants: Vec<TraitConstant>,
    pub types: Vec<TraitType>,

    pub name: Ident,
    pub generics: Vec<TraitGeneric>,
    pub span: Span,

    /// When resolving the types of Trait elements, all references to `Self` resolve
    /// to this TypeVariable. Then when we check if the types of trait impl elements
    /// match the definition in the trait, we bind this TypeVariable to whatever
    /// the correct Self type is for that particular impl block.
    pub self_type_typevar_id: TypeVariableId,
    pub self_type_typevar: TypeVariable,
}

impl Trait {
    pub fn bind_generics(&self, types: &Vec<Type>) {
        assert!(self.generics.len() == types.len());

        for (generic, typ) in self.generics.iter().zip(types) {
            *generic.typevar.borrow_mut() = TypeBinding::Bound(typ.clone());
        }
    }

    pub fn unbind_generics(&self) {
        for generic in self.generics.iter() {
            *generic.typevar.borrow_mut() = TypeBinding::Unbound(generic.typevar_id);
        }
    }
}

pub struct TraitImpl {
    pub ident: Ident,
    pub typ: Type,
    pub trait_id: TraitId,
    pub methods: Vec<FuncId>, // methods[i] is the implementation of trait.methods[i] for Type typ
}

#[derive(Debug, Clone)]
pub struct TraitConstraint {
    pub typ: Type,
    pub trait_id: Option<TraitId>,
    pub trait_generics: Vec<Type>,
}

impl std::hash::Hash for Trait {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialEq for Trait {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Trait {
    pub fn new(
        id: TraitId,
        name: Ident,
        span: Span,
        generics: Vec<TraitGeneric>,
        self_type_typevar_id: TypeVariableId,
        self_type_typevar: TypeVariable,
    ) -> Trait {
        Trait {
            id,
            name,
            span,
            methods: Vec::new(),
            constants: Vec::new(),
            types: Vec::new(),
            generics,
            self_type_typevar_id,
            self_type_typevar,
        }
    }

    pub fn set_methods(&mut self, methods: Vec<TraitFunction>) {
        self.methods = methods;
    }
}

impl std::fmt::Display for Trait {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl TraitFunction {
    pub fn get_type(&self) -> Type {
        Type::Function(
            self.parameters.clone(),
            Box::new(self.return_type.clone()),
            Box::new(Type::Unit),
        )
    }
}
