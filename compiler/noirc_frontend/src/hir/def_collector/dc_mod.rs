use std::collections::HashSet;

use fm::FileId;
use noirc_errors::Location;

use crate::{
    graph::CrateId,
    hir::def_collector::dc_crate::{UnresolvedStruct, UnresolvedTrait},
    node_interner::TraitId,
    parser::SubModule,
    FunctionDefinition, Ident, LetStatement, NoirFunction, NoirStruct, NoirTrait, NoirTypeAlias,
    ParsedModule, TraitImpl, TraitImplItem, TraitItem, TypeImpl,
};

use super::{
    dc_crate::{
        CompilationErrors, DefCollector, UnresolvedFunctions, UnresolvedGlobal,
        UnresolvedTraitImpl, UnresolvedTypeAlias,
    },
    errors::{DefCollectorErrorKind, DuplicateType},
};
use crate::hir::def_map::{parse_file, LocalModuleId, ModuleData, ModuleDefId, ModuleId};
use crate::hir::resolution::import::ImportDirective;
use crate::hir::Context;

/// Given a module collect all definitions into ModuleData
struct ModCollector<'a> {
    pub(crate) def_collector: &'a mut DefCollector,
    pub(crate) file_id: FileId,
    pub(crate) module_id: LocalModuleId,
}

/// Walk a module and collect its definitions.
///
/// This performs the entirety of the definition collection phase of the name resolution pass.
pub fn collect_defs(
    def_collector: &mut DefCollector,
    ast: ParsedModule,
    file_id: FileId,
    module_id: LocalModuleId,
    crate_id: CrateId,
    context: &mut Context,
) -> CompilationErrors {
    let mut collector = ModCollector { def_collector, file_id, module_id };
    let mut errors = CompilationErrors::default();
    // First resolve the module declarations
    for decl in ast.module_decls {
        errors.extend_all(collector.parse_module_declaration(context, &decl, crate_id));
    }

    errors.extend_all(collector.collect_submodules(context, crate_id, ast.submodules, file_id));

    // Then add the imports to defCollector to resolve once all modules in the hierarchy have been resolved
    for import in ast.imports {
        collector.def_collector.collected_imports.push(ImportDirective {
            module_id: collector.module_id,
            path: import.path,
            alias: import.alias,
        });
    }

    errors.def_errors.extend(collector.collect_globals(context, ast.globals));

    errors.def_errors.extend(collector.collect_traits(ast.traits, crate_id));

    errors.def_errors.extend(collector.collect_structs(context, ast.types, crate_id));

    errors.def_errors.extend(collector.collect_type_aliases(context, ast.type_aliases));

    errors.def_errors.extend(collector.collect_functions(context, ast.functions));

    errors.def_errors.extend(collector.collect_trait_impls(context, ast.trait_impls));

    collector.collect_impls(context, ast.impls);

    errors
}

impl<'a> ModCollector<'a> {
    fn collect_globals(
        &mut self,
        context: &mut Context,
        globals: Vec<LetStatement>,
    ) -> Vec<(DefCollectorErrorKind, fm::FileId)> {
        let mut errors = vec![];
        for global in globals {
            let name = global.pattern.name_ident().clone();

            // First create dummy function in the DefInterner
            // So that we can get a StmtId
            let stmt_id = context.def_interner.push_empty_global();

            // Add the statement to the scope so its path can be looked up later
            let result =
                self.def_collector.def_map.modules[self.module_id.0].declare_global(name, stmt_id);

            if let Err((first_def, second_def)) = result {
                let err = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::Global,
                    first_def,
                    second_def,
                };
                errors.push((err, self.file_id));
            }

            self.def_collector.collected_globals.push(UnresolvedGlobal {
                file_id: self.file_id,
                module_id: self.module_id,
                stmt_id,
                stmt_def: global,
            });
        }
        errors
    }

    fn collect_impls(&mut self, context: &mut Context, impls: Vec<TypeImpl>) {
        for r#impl in impls {
            let mut unresolved_functions =
                UnresolvedFunctions { file_id: self.file_id, functions: Vec::new() };

            for method in r#impl.methods {
                let func_id = context.def_interner.push_empty_fn();
                context.def_interner.push_function_definition(method.name().to_owned(), func_id);
                unresolved_functions.push_fn(self.module_id, func_id, method);
            }

            let key = (r#impl.object_type, self.module_id);
            let methods = self.def_collector.collected_impls.entry(key).or_default();
            methods.push((r#impl.generics, r#impl.type_span, unresolved_functions));
        }
    }

    fn collect_trait_impls(
        &mut self,
        context: &mut Context,
        impls: Vec<TraitImpl>,
    ) -> Vec<(DefCollectorErrorKind, fm::FileId)> {
        let mut diagnostics: Vec<(DefCollectorErrorKind, fm::FileId)> = vec![];
        for trait_impl in impls {
            let trait_name = trait_impl.trait_name.clone();
            let module = &self.def_collector.def_map.modules[self.module_id.0];
            match module.find_name(&trait_name).types {
                Some((module_def_id, _visibility)) => {
                    if let Some(collected_trait) = self.get_unresolved_trait(module_def_id) {
                        let unresolved_functions = self.collect_trait_implementations(
                            context,
                            &trait_impl,
                            &collected_trait.trait_def,
                            &mut diagnostics,
                        );

                        for (_, func_id, noir_function) in &unresolved_functions.functions {
                            let name = noir_function.name().to_owned();

                            context.def_interner.push_function_definition(name, *func_id);
                        }

                        let unresolved_trait_impl = UnresolvedTraitImpl {
                            file_id: self.file_id,
                            module_id: self.module_id,
                            the_trait: collected_trait,
                            methods: unresolved_functions,
                            trait_impl_ident: trait_impl.trait_name.clone(),
                        };

                        let trait_id = match module_def_id {
                            ModuleDefId::TraitId(trait_id) => trait_id,
                            _ => unreachable!(),
                        };

                        let key = (trait_impl.object_type, self.module_id, trait_id);
                        self.def_collector
                            .collected_traits_impls
                            .insert(key, unresolved_trait_impl);
                    } else {
                        diagnostics.push((
                            DefCollectorErrorKind::NotATrait {
                                not_a_trait_name: trait_name.clone(),
                            },
                            self.file_id,
                        ));
                    }
                }
                None => {
                    diagnostics.push((
                        DefCollectorErrorKind::TraitNotFound { trait_ident: trait_name },
                        self.file_id,
                    ));
                }
            }
        }

        diagnostics
    }

    fn get_unresolved_trait(&self, module_def_id: ModuleDefId) -> Option<UnresolvedTrait> {
        match module_def_id {
            ModuleDefId::TraitId(trait_id) => {
                self.def_collector.collected_traits.get(&trait_id).cloned()
            }
            _ => None,
        }
    }

    fn collect_trait_implementations(
        &mut self,
        context: &mut Context,
        trait_impl: &TraitImpl,
        trait_def: &NoirTrait,
        diagnostics: &mut Vec<(DefCollectorErrorKind, FileId)>,
    ) -> UnresolvedFunctions {
        let mut unresolved_functions =
            UnresolvedFunctions { file_id: self.file_id, functions: Vec::new() };

        for item in &trait_impl.items {
            if let TraitImplItem::Function(impl_method) = item {
                let func_id = context.def_interner.push_empty_fn();
                context
                    .def_interner
                    .push_function_definition(impl_method.name().to_owned(), func_id);
                unresolved_functions.push_fn(self.module_id, func_id, impl_method.clone());
            }
        }

        // set of function ids that have a corresponding method in the trait
        let mut func_ids_in_trait = HashSet::new();

        for item in &trait_def.items {
            // TODO(Maddiaa): Investigate trait implementations with attributes see: https://github.com/noir-lang/noir/issues/2629
            if let TraitItem::Function {
                name,
                generics,
                parameters,
                return_type,
                where_clause,
                body,
            } = item
            {
                // List of functions in the impl block with the same name as the method
                //  `matching_fns.len() == 0`  => missing method impl
                //  `matching_fns.len() > 1`   => duplicate definition (collect_functions will throw a Duplicate error)
                let matching_fns: Vec<_> = unresolved_functions
                    .functions
                    .iter()
                    .filter(|(_, _, func_impl)| func_impl.name() == name.0.contents)
                    .collect();

                if matching_fns.is_empty() {
                    match body {
                        Some(body) => {
                            // if there's a default implementation for the method, use it
                            let method_name = name.0.contents.clone();
                            let func_id = context.def_interner.push_empty_fn();
                            context.def_interner.push_function_definition(method_name, func_id);
                            let impl_method = NoirFunction::normal(FunctionDefinition::normal(
                                name,
                                generics,
                                parameters,
                                body,
                                where_clause,
                                return_type,
                            ));
                            func_ids_in_trait.insert(func_id);
                            unresolved_functions.push_fn(self.module_id, func_id, impl_method);
                        }
                        None => {
                            let error = DefCollectorErrorKind::TraitMissingMethod {
                                trait_name: trait_def.name.clone(),
                                method_name: name.clone(),
                                trait_impl_span: trait_impl.object_type_span,
                            };
                            diagnostics.push((error, self.file_id));
                        }
                    }
                } else {
                    for (_, func_id, _) in &matching_fns {
                        func_ids_in_trait.insert(*func_id);
                    }
                }
            }
        }

        // Emit MethodNotInTrait error for methods in the impl block that
        // don't have a corresponding method signature defined in the trait
        for (_, func_id, func) in &unresolved_functions.functions {
            if !func_ids_in_trait.contains(func_id) {
                let error = DefCollectorErrorKind::MethodNotInTrait {
                    trait_name: trait_def.name.clone(),
                    impl_method: func.name_ident().clone(),
                };
                diagnostics.push((error, self.file_id));
            }
        }

        unresolved_functions
    }

    fn collect_functions(
        &mut self,
        context: &mut Context,
        functions: Vec<NoirFunction>,
    ) -> Vec<(DefCollectorErrorKind, FileId)> {
        let mut unresolved_functions =
            UnresolvedFunctions { file_id: self.file_id, functions: Vec::new() };
        let mut definiton_errors = vec![];

        for function in functions {
            let name = function.name_ident().clone();

            // First create dummy function in the DefInterner
            // So that we can get a FuncId
            let func_id = context.def_interner.push_empty_fn();
            context.def_interner.push_function_definition(name.0.contents.clone(), func_id);

            // Now link this func_id to a crate level map with the noir function and the module id
            // Encountering a NoirFunction, we retrieve it's module_data to get the namespace
            // Once we have lowered it to a HirFunction, we retrieve it's Id from the DefInterner
            // and replace it
            // With this method we iterate each function in the Crate and not each module
            // This may not be great because we have to pull the module_data for each function
            unresolved_functions.push_fn(self.module_id, func_id, function);

            // Add function to scope/ns of the module
            let result = self.def_collector.def_map.modules[self.module_id.0]
                .declare_function(name, func_id);

            if let Err((first_def, second_def)) = result {
                let error = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::Function,
                    first_def,
                    second_def,
                };
                definiton_errors.push((error, self.file_id));
            }
        }

        self.def_collector.collected_functions.push(unresolved_functions);
        definiton_errors
    }

    /// Collect any struct definitions declared within the ast.
    /// Returns a vector of errors if any structs were already defined.
    fn collect_structs(
        &mut self,
        context: &mut Context,
        types: Vec<NoirStruct>,
        krate: CrateId,
    ) -> Vec<(DefCollectorErrorKind, FileId)> {
        let mut definiton_errors = vec![];
        for struct_definition in types {
            let name = struct_definition.name.clone();

            let unresolved = UnresolvedStruct {
                file_id: self.file_id,
                module_id: self.module_id,
                struct_def: struct_definition,
            };

            // Create the corresponding module for the struct namespace
            let id = match self.push_child_module(&name, self.file_id, false, false) {
                Ok(local_id) => context.def_interner.new_struct(&unresolved, krate, local_id),
                Err(error) => {
                    definiton_errors.push((error, self.file_id));
                    continue;
                }
            };

            // Add the struct to scope so its path can be looked up later
            let result =
                self.def_collector.def_map.modules[self.module_id.0].declare_struct(name, id);

            if let Err((first_def, second_def)) = result {
                let error = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::TypeDefinition,
                    first_def,
                    second_def,
                };
                definiton_errors.push((error, self.file_id));
            }

            // And store the TypeId -> StructType mapping somewhere it is reachable
            self.def_collector.collected_types.insert(id, unresolved);
        }
        definiton_errors
    }

    /// Collect any type aliases definitions declared within the ast.
    /// Returns a vector of errors if any type aliases were already defined.
    fn collect_type_aliases(
        &mut self,
        context: &mut Context,
        type_aliases: Vec<NoirTypeAlias>,
    ) -> Vec<(DefCollectorErrorKind, FileId)> {
        let mut def_errors: Vec<(DefCollectorErrorKind, FileId)> = vec![];
        for type_alias in type_aliases {
            let name = type_alias.name.clone();

            // And store the TypeId -> TypeAlias mapping somewhere it is reachable
            let unresolved = UnresolvedTypeAlias {
                file_id: self.file_id,
                module_id: self.module_id,
                type_alias_def: type_alias,
            };

            let type_alias_id = context.def_interner.push_type_alias(&unresolved);

            // Add the type alias to scope so its path can be looked up later
            let result = self.def_collector.def_map.modules[self.module_id.0]
                .declare_type_alias(name, type_alias_id);

            if let Err((first_def, second_def)) = result {
                let err = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::Function,
                    first_def,
                    second_def,
                };
                def_errors.push((err, self.file_id));
            }

            self.def_collector.collected_type_aliases.insert(type_alias_id, unresolved);
        }
        def_errors
    }

    /// Collect any traits definitions declared within the ast.
    /// Returns a vector of errors if any traits were already defined.
    fn collect_traits(
        &mut self,
        traits: Vec<NoirTrait>,
        krate: CrateId,
    ) -> Vec<(DefCollectorErrorKind, FileId)> {
        let mut def_errors: Vec<(DefCollectorErrorKind, FileId)> = vec![];
        for trait_definition in traits {
            let name = trait_definition.name.clone();

            // Create the corresponding module for the trait namespace
            let id = match self.push_child_module(&name, self.file_id, false, false) {
                Ok(local_id) => TraitId(ModuleId { krate, local_id }),
                Err(error) => {
                    def_errors.push((error, self.file_id));
                    continue;
                }
            };

            // Add the trait to scope so its path can be looked up later
            let result =
                self.def_collector.def_map.modules[self.module_id.0].declare_trait(name, id);

            if let Err((first_def, second_def)) = result {
                let error = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::Trait,
                    first_def,
                    second_def,
                };
                def_errors.push((error, self.file_id));
            }

            // And store the TraitId -> TraitType mapping somewhere it is reachable
            let unresolved = UnresolvedTrait {
                file_id: self.file_id,
                module_id: self.module_id,
                trait_def: trait_definition,
            };
            self.def_collector.collected_traits.insert(id, unresolved);
        }
        def_errors
    }

    fn collect_submodules(
        &mut self,
        context: &mut Context,
        crate_id: CrateId,
        submodules: Vec<SubModule>,
        file_id: FileId,
    ) -> CompilationErrors {
        let mut errors = CompilationErrors::default();
        for submodule in submodules {
            match self.push_child_module(&submodule.name, file_id, true, submodule.is_contract) {
                Ok(child) => {
                    errors.extend_all(collect_defs(
                        self.def_collector,
                        submodule.contents,
                        file_id,
                        child,
                        crate_id,
                        context,
                    ));
                }
                Err(error) => {
                    errors.def_errors.push((error, file_id));
                }
            };
        }
        errors
    }

    /// Search for a module named `mod_name`
    /// Parse it, add it as a child to the parent module in which it was declared
    /// and then collect all definitions of the child module
    fn parse_module_declaration(
        &mut self,
        context: &mut Context,
        mod_name: &Ident,
        crate_id: CrateId,
    ) -> CompilationErrors {
        let mut errors = CompilationErrors::default();
        let child_file_id =
            match context.file_manager.find_module(self.file_id, &mod_name.0.contents) {
                Ok(child_file_id) => child_file_id,
                Err(_) => {
                    let err =
                        DefCollectorErrorKind::UnresolvedModuleDecl { mod_name: mod_name.clone() };
                    errors.def_errors.push((err, self.file_id));
                    return errors;
                }
            };

        // Parse the AST for the module we just found and then recursively look for it's defs
        //let ast = parse_file(&context.file_manager, child_file_id, errors);
        let (ast, parsing_errors) = parse_file(&context.file_manager, child_file_id);

        errors.extend_parser_errors(parsing_errors, child_file_id);

        // Add module into def collector and get a ModuleId
        match self.push_child_module(mod_name, child_file_id, true, false) {
            Ok(child_mod_id) => {
                errors.extend_all(collect_defs(
                    self.def_collector,
                    ast,
                    child_file_id,
                    child_mod_id,
                    crate_id,
                    context,
                ));
            }
            Err(error) => {
                errors.def_errors.push((error, child_file_id));
            }
        }
        errors
    }

    /// Add a child module to the current def_map.
    /// On error this returns None and pushes to `errors`
    fn push_child_module(
        &mut self,
        mod_name: &Ident,
        file_id: FileId,
        add_to_parent_scope: bool,
        is_contract: bool,
    ) -> Result<LocalModuleId, DefCollectorErrorKind> {
        let parent = Some(self.module_id);
        let location = Location::new(mod_name.span(), file_id);
        let new_module = ModuleData::new(parent, location, is_contract);
        let module_id = self.def_collector.def_map.modules.insert(new_module);

        let modules = &mut self.def_collector.def_map.modules;

        // Update the parent module to reference the child
        modules[self.module_id.0].children.insert(mod_name.clone(), LocalModuleId(module_id));

        // Add this child module into the scope of the parent module as a module definition
        // module definitions are definitions which can only exist at the module level.
        // ModuleDefinitionIds can be used across crates since they contain the CrateId
        //
        // We do not want to do this in the case of struct modules (each struct type corresponds
        // to a child module containing its methods) since the module name should not shadow
        // the struct name.
        if add_to_parent_scope {
            let mod_id = ModuleId {
                krate: self.def_collector.def_map.krate,
                local_id: LocalModuleId(module_id),
            };

            if let Err((first_def, second_def)) =
                modules[self.module_id.0].declare_child_module(mod_name.to_owned(), mod_id)
            {
                let err = DefCollectorErrorKind::Duplicate {
                    typ: DuplicateType::Module,
                    first_def,
                    second_def,
                };
                return Err(err);
            }
        }

        Ok(LocalModuleId(module_id))
    }
}
