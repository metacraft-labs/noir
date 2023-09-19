// XXX: These tests repeat a lot of code
// what we should do is have test cases which are passed to a test harness
// A test harness will allow for more expressive and readable tests
#[cfg(test)]
mod test {

    use core::panic;
    use std::collections::BTreeMap;

    use fm::FileId;
    use noirc_errors::Location;

    use crate::hir::def_collector::errors::{DefCollectorErrorKind, DuplicateType};
    use crate::hir::def_map::ModuleData;
    use crate::hir::resolution::errors::ResolverError;
    use crate::hir::resolution::import::PathResolutionError;
    use crate::hir::type_check::TypeCheckError;
    use crate::hir::Context;
    use crate::node_interner::{NodeInterner, StmtId};

    use crate::graph::CrateGraph;
    use crate::hir::def_collector::dc_crate::{CompilationErrors, DefCollector};
    use crate::hir_def::expr::HirExpression;
    use crate::hir_def::stmt::HirStatement;
    use crate::monomorphization::monomorphize;
    use crate::ParsedModule;
    use crate::{
        hir::def_map::{CrateDefMap, LocalModuleId},
        parse_program,
    };
    use arena::Arena;
    use fm::FileManager;

    pub(crate) fn get_program(src: &str) -> (ParsedModule, Context, CompilationErrors) {
        let root = std::path::Path::new("/");
        let fm = FileManager::new(root);
        let graph = CrateGraph::default();
        let mut context = Context::new(fm, graph);
        let root_file_id = FileId::dummy();
        let root_crate_id = context.crate_graph.add_crate_root(root_file_id);
        let (program, parser_errors) = parse_program(src);
        let mut errors = CompilationErrors::default();
        errors.extend_parser_errors(parser_errors, root_file_id);
        if !errors.has_parser_errors() {
            // Allocate a default Module for the root, giving it a ModuleId
            let mut modules: Arena<ModuleData> = Arena::default();
            let location = Location::new(Default::default(), root_file_id);
            let root = modules.insert(ModuleData::new(None, location, false));
            let def_map = CrateDefMap {
                root: LocalModuleId(root),
                modules,
                krate: root_crate_id,
                extern_prelude: BTreeMap::new(),
            };
            // Now we want to populate the CrateDefMap using the DefCollector
            errors.extend_all(DefCollector::collect(
                def_map,
                &mut context,
                program.clone(),
                root_file_id,
            ));
        }
        (program, context, errors)
    }

    pub(crate) fn get_program_errors(src: &str) -> CompilationErrors {
        let (_program, _context, errors) = get_program(src);
        errors
    }

    #[test]
    fn check_trait_implementation_duplicate_method() {
        let src = "
        trait Default {
            fn default(x: Field, y: Field) -> Field;
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        impl Default for Foo {
            // Duplicate trait methods should not compile
            fn default(x: Field, y: Field) -> Field {
                y + 2 * x
            }
            // Duplicate trait methods should not compile
            fn default(x: Field, y: Field) -> Field {
                x + 2 * y
            }
        }
        
        fn main() {}";

        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 1,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.def_errors {
            match &err {
                (DefCollectorErrorKind::Duplicate { typ, first_def, second_def }, _file_id) => {
                    assert_eq!(typ, &DuplicateType::TraitImplementation);
                    assert_eq!(first_def, "default");
                    assert_eq!(second_def, "default");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_method_return_type() {
        let src = "
        trait Default {
            fn default() -> Self;
        }
        
        struct Foo {
        }
        
        impl Default for Foo {
            fn default() -> Field {
                0
            }
        }
        
        fn main() {
        }
        ";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 0,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 1,
            "Expected 1 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.type_errors {
            match &err {
                (
                    TypeCheckError::TypeMismatch { expected_typ, expr_typ, expr_span: _ },
                    _file_id,
                ) => {
                    assert_eq!(expected_typ, "Foo");
                    assert_eq!(expr_typ, "Field");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_method_return_type2() {
        let src = "
        trait Default {
            fn default(x: Field, y: Field) -> Self;
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        impl Default for Foo {
            fn default(x: Field, _y: Field) -> Field {
                x
            }
        }
        
        fn main() {
        }";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 0,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 1,
            "Expected 1 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.type_errors {
            match &err {
                (
                    TypeCheckError::TypeMismatch { expected_typ, expr_typ, expr_span: _ },
                    _file_id,
                ) => {
                    assert_eq!(expected_typ, "Foo");
                    assert_eq!(expr_typ, "Field");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_missing_implementation() {
        let src = "
        trait Default {
            fn default(x: Field, y: Field) -> Self;
        
            fn method2(x: Field) -> Field;
        
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        impl Default for Foo {
            fn default(x: Field, y: Field) -> Self {
                Self { bar: x, array: [x,y] }
            }
        }
        
        fn main() {
        }
        ";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 1,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.def_errors {
            match &err {
                (
                    DefCollectorErrorKind::TraitMissingMethod {
                        trait_name,
                        method_name,
                        trait_impl_span: _,
                    },
                    _file_id,
                ) => {
                    assert_eq!(trait_name, "Default");
                    assert_eq!(method_name, "method2");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_not_in_scope() {
        let src = "
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        // Default trait does not exist
        impl Default for Foo {
            fn default(x: Field, y: Field) -> Self {
                Self { bar: x, array: [x,y] }
            }
        }
        
        fn main() {
        }
        
        ";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 1,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.def_errors {
            match &err {
                (DefCollectorErrorKind::TraitNotFound { trait_ident }, _file_id) => {
                    assert_eq!(trait_ident, "Default");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_method_name() {
        let src = "
        trait Default {
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        // wrong trait name method should not compile
        impl Default for Foo {
            fn doesnt_exist(x: Field, y: Field) -> Self {
                Self { bar: x, array: [x,y] }
            }
        }
        
        fn main() {
        }";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 1,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.def_errors {
            match &err {
                (DefCollectorErrorKind::MethodNotInTrait { trait_name, impl_method }, _file_id) => {
                    assert_eq!(trait_name, "Default");
                    assert_eq!(impl_method, "doesnt_exist");
                }
                _ => {
                    assert!(false, "No other errors are expected in this test case!");
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_parameter() {
        let src = "
        trait Default {
            fn default(x: Field) -> Self;
        }
        
        struct Foo {
            bar: u32,
        }
        
        impl Default for Foo {
            fn default(x: u32) -> Self {
                Foo {bar: x}
            }
        }
        
        fn main() {
        }
        ";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 0,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 1,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.type_errors {
            match &err {
                (
                    TypeCheckError::TraitMethodParameterTypeMismatch {
                        method_name,
                        expected_typ,
                        actual_typ,
                        ..
                    },
                    _file_id,
                ) => {
                    assert_eq!(method_name, "default");
                    assert_eq!(expected_typ, "Field");
                    assert_eq!(actual_typ, "u32");
                }
                _ => {
                    assert!(
                        false,
                        "No other errors are expected in this test case! Found = {:?}",
                        err
                    );
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_parameter2() {
        let src = "
        trait Default {
            fn default(x: Field, y: Field) -> Self;
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        impl Default for Foo {
            fn default(x: Field, y: Foo) -> Self {
                Self { bar: x, array: [x, y.bar] }
            }
        }
        
        fn main() {
        }";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 0,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 1,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.type_errors {
            match &err {
                (
                    TypeCheckError::TraitMethodParameterTypeMismatch {
                        method_name,
                        expected_typ,
                        actual_typ,
                        ..
                    },
                    _file_id,
                ) => {
                    assert_eq!(method_name, "default");
                    assert_eq!(expected_typ, "Field");
                    assert_eq!(actual_typ, "Foo");
                }
                _ => {
                    assert!(
                        false,
                        "No other errors are expected in this test case! Found = {:?}",
                        err
                    );
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_parameter_type() {
        let src = "
        trait Default {
            fn default(x: Field, y: NotAType) -> Field;
        }
        
        fn main(x: Field, y: Field) {
            assert(y == x);
        }";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 1,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 0,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.resolver_errors {
            match &err {
                (ResolverError::PathResolutionError(path_solution_error), _file_id) => {
                    match path_solution_error {
                        PathResolutionError::Unresolved(ident) => {
                            assert_eq!(ident, "NotAType");
                        }
                        PathResolutionError::ExternalContractUsed(_) => {
                            assert!(
                                false,
                                "No other errors are expected in this test case! Found = {:?}",
                                err
                            );
                        }
                    }
                }
                _ => {
                    assert!(
                        false,
                        "No other errors are expected in this test case! Found = {:?}",
                        err
                    );
                }
            };
        }
    }

    #[test]
    fn check_trait_wrong_parameters_count() {
        let src = "
        trait Default {
            fn default(x: Field, y: Field) -> Self;
        }
        
        struct Foo {
            bar: Field,
            array: [Field; 2],
        }
        
        impl Default for Foo {
            fn default(x: Field) -> Self {
                Self { bar: x, array: [x, x] }
            }
        }
        
        fn main() {
        }
        ";
        let compilator_errors = get_program_errors(src);
        assert!(!compilator_errors.has_parser_errors());
        assert!(
            compilator_errors.resolver_errors.len() == 0,
            "Expected 0 resolver errors, got: {:?}",
            compilator_errors.resolver_errors
        );
        assert!(
            compilator_errors.def_errors.len() == 1,
            "Expected 0 def collector errors, got: {:?}",
            compilator_errors.def_errors
        );
        assert!(
            compilator_errors.type_errors.len() == 0,
            "Expected 0 type check error, got: {:?}",
            compilator_errors.type_errors
        );
        for err in compilator_errors.def_errors {
            match &err {
                (
                    DefCollectorErrorKind::MismatchTraitImplementationNumParameters {
                        actual_num_parameters,
                        expected_num_parameters,
                        trait_name,
                        method_name,
                        ..
                    },
                    _file_id,
                ) => {
                    assert_eq!(actual_num_parameters, &(1 as usize));
                    assert_eq!(expected_num_parameters, &(2 as usize));
                    assert_eq!(method_name, "default");
                    assert_eq!(trait_name, "Default");
                }
                _ => {
                    assert!(
                        false,
                        "No other errors are expected in this test case! Found = {:?}",
                        err
                    );
                }
            };
        }
    }

    fn get_program_captures(src: &str) -> Vec<Vec<String>> {
        let (program, context, _errors) = get_program(src);
        let interner = context.def_interner;
        let mut all_captures: Vec<Vec<String>> = Vec::new();
        for func in program.functions {
            let func_id = interner.find_function(&func.name().to_string()).unwrap();
            let hir_func = interner.function(&func_id);
            // Iterate over function statements and apply filtering function
            parse_statement_blocks(
                hir_func.block(&interner).statements(),
                &interner,
                &mut all_captures,
            );
        }
        all_captures
    }

    fn parse_statement_blocks(
        stmts: &[StmtId],
        interner: &NodeInterner,
        result: &mut Vec<Vec<String>>,
    ) {
        let mut expr: HirExpression;

        for stmt_id in stmts.iter() {
            let hir_stmt = interner.statement(stmt_id);
            match hir_stmt {
                HirStatement::Expression(expr_id) => {
                    expr = interner.expression(&expr_id);
                }
                HirStatement::Let(let_stmt) => {
                    expr = interner.expression(&let_stmt.expression);
                }
                HirStatement::Assign(assign_stmt) => {
                    expr = interner.expression(&assign_stmt.expression);
                }
                HirStatement::Constrain(constr_stmt) => {
                    expr = interner.expression(&constr_stmt.0);
                }
                HirStatement::Semi(semi_expr) => {
                    expr = interner.expression(&semi_expr);
                }
                HirStatement::Error => panic!("Invalid HirStatement!"),
            }
            get_lambda_captures(expr, interner, result); // TODO: dyn filter function as parameter
        }
    }

    fn get_lambda_captures(
        expr: HirExpression,
        interner: &NodeInterner,
        result: &mut Vec<Vec<String>>,
    ) {
        if let HirExpression::Lambda(lambda_expr) = expr {
            let mut cur_capture = Vec::new();

            for capture in lambda_expr.captures.iter() {
                cur_capture.push(interner.definition(capture.ident.id).name.clone());
            }
            result.push(cur_capture);

            // Check for other captures recursively within the lambda body
            let hir_body_expr = interner.expression(&lambda_expr.body);
            if let HirExpression::Block(block_expr) = hir_body_expr {
                parse_statement_blocks(block_expr.statements(), interner, result);
            }
        }
    }

    #[test]
    fn resolve_empty_function() {
        let src = "
            fn main() {

            }
        ";
        assert!(get_program_errors(src).is_empty());
    }
    #[test]
    fn resolve_basic_function() {
        let src = r#"
            fn main(x : Field) {
                let y = x + x;
                assert(y == x);
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }
    #[test]
    fn resolve_unused_var() {
        let src = r#"
            fn main(x : Field) {
                let y = x + x;
                assert(x == x);
            }
        "#;

        let errors = get_program_errors(src);

        // There should only be one error
        assert!(
            errors.resolver_errors.len() == 1,
            "Expected 1 error, got: {:?}",
            errors.resolver_errors
        );

        // It should be regarding the unused variable
        match &errors.resolver_errors[0] {
            (ResolverError::UnusedVariable { ident }, _file_id) => {
                assert_eq!(&ident.0.contents, "y");
            }
            _ => unreachable!("we should only have an unused var error"),
        }
    }

    #[test]
    fn resolve_unresolved_var() {
        let src = r#"
            fn main(x : Field) {
                let y = x + x;
                assert(y == z);
            }
        "#;
        let errors = get_program_errors(src);
        assert_eq!(errors.resolver_errors.len(), 1);

        // It should be regarding the unresolved var `z` (Maybe change to undeclared and special case)
        match &errors.resolver_errors[0].0 {
            ResolverError::VariableNotDeclared { name, span: _ } => assert_eq!(name, "z"),
            _ => unimplemented!("we should only have an unresolved variable"),
        }
    }

    #[test]
    fn unresolved_path() {
        let src = "
            fn main(x : Field) {
                let _z = some::path::to::a::func(x);
            }
        ";
        let errors = get_program_errors(src);
        assert_eq!(errors.resolver_errors.len(), 1);
        match &errors.resolver_errors[0].0 {
            ResolverError::PathResolutionError(PathResolutionError::Unresolved(name)) => {
                assert_eq!(name.to_string(), "some");
            }
            _ => unimplemented!("we should only have an unresolved function"),
        }
    }

    #[test]
    fn resolve_literal_expr() {
        let src = r#"
            fn main(x : Field) {
                let y = 5;
                assert(y == x);
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn multiple_resolution_errors() {
        let src = r#"
            fn main(x : Field) {
               let y = foo::bar(x);
               let z = y + a;
            }
        "#;

        let errors = get_program_errors(src);
        assert!(
            errors.resolver_errors.len() == 3,
            "Expected 3 errors, got: {:?}",
            errors.resolver_errors
        );

        // Errors are:
        // `a` is undeclared
        // `z` is unused
        // `foo::bar` does not exist
        for err in errors.resolver_errors {
            match &err {
                (ResolverError::UnusedVariable { ident }, _file_id) => {
                    assert_eq!(&ident.0.contents, "z");
                }
                (ResolverError::VariableNotDeclared { name, .. }, _file_id) => {
                    assert_eq!(name, "a");
                }
                (
                    ResolverError::PathResolutionError(PathResolutionError::Unresolved(name)),
                    _file_id,
                ) => {
                    assert_eq!(name.to_string(), "foo");
                }
                _ => unimplemented!(),
            };
        }
    }

    #[test]
    fn resolve_prefix_expr() {
        let src = r#"
            fn main(x : Field) {
                let _y = -x;
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn resolve_for_expr() {
        let src = r#"
            fn main(x : Field) {
                for i in 1..20 {
                    let _z = x + i;
                };
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn resolve_call_expr() {
        let src = r#"
            fn main(x : Field) {
                let _z = foo(x);
            }

            fn foo(x : Field) -> Field {
                x
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn resolve_shadowing() {
        let src = r#"
            fn main(x : Field) {
                let x = foo(x);
                let x = x;
                let (x, x) = (x, x);
                let _ = x;
            }

            fn foo(x : Field) -> Field {
                x
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn resolve_basic_closure() {
        let src = r#"
            fn main(x : Field) -> pub Field {
                let closure = |y| y + x;
                closure(x)
            }
        "#;
        assert!(get_program_errors(src).is_empty());
    }

    #[test]
    fn resolve_simplified_closure() {
        // based on bug https://github.com/noir-lang/noir/issues/1088

        let src = r#"fn do_closure(x: Field) -> Field {
            let y = x;
            let ret_capture = || {
              y
            };
            ret_capture()
          }

          fn main(x: Field) {
              assert(do_closure(x) == 100);
          }

          "#;
        let parsed_captures = get_program_captures(src);
        let expected_captures = vec![vec!["y".to_string()]];
        assert_eq!(expected_captures, parsed_captures);
    }

    #[test]
    fn resolve_complex_closures() {
        let src = r#"
            fn main(x: Field) -> pub Field {
                let closure_without_captures = |x| x + x;
                let a = closure_without_captures(1);

                let closure_capturing_a_param = |y| y + x;
                let b = closure_capturing_a_param(2);

                let closure_capturing_a_local_var = |y| y + b;
                let c = closure_capturing_a_local_var(3);

                let closure_with_transitive_captures = |y| {
                    let d = 5;
                    let nested_closure = |z| {
                        let doubly_nested_closure = |w| w + x + b;
                        a + z + y + d + x + doubly_nested_closure(4) + x + y
                    };
                    let res = nested_closure(5);
                    res
                };

                a + b + c + closure_with_transitive_captures(6)
            }
        "#;
        assert!(get_program_errors(src).is_empty(), "there should be no errors");

        let expected_captures = vec![
            vec![],
            vec!["x".to_string()],
            vec!["b".to_string()],
            vec!["x".to_string(), "b".to_string(), "a".to_string()],
            vec![
                "x".to_string(),
                "b".to_string(),
                "a".to_string(),
                "y".to_string(),
                "d".to_string(),
            ],
            vec!["x".to_string(), "b".to_string()],
        ];

        let parsed_captures = get_program_captures(src);

        assert_eq!(expected_captures, parsed_captures);
    }

    #[test]
    fn resolve_fmt_strings() {
        let src = r#"
            fn main() {
                let string = f"this is i: {i}";
                println(string);

                println(f"I want to print {0}");

                let new_val = 10;
                println(f"randomstring{new_val}{new_val}");
            }
            fn println<T>(x : T) -> T {
                x
            }
        "#;

        let errors = get_program_errors(src);

        assert!(
            errors.resolver_errors.len() == 2,
            "Expected 2 errors, got: {:?}",
            errors.resolver_errors
        );

        for err in errors.resolver_errors {
            match &err {
                (ResolverError::VariableNotDeclared { name, .. }, _file_id) => {
                    assert_eq!(name, "i");
                }
                (ResolverError::NumericConstantInFormatString { name, .. }, _file_id) => {
                    assert_eq!(name, "0");
                }
                _ => unimplemented!(),
            };
        }
    }

    fn check_rewrite(src: &str, expected: &str) {
        let (_program, context, _errors) = get_program(src);
        let main_func_id = context.def_interner.find_function("main").unwrap();
        let program = monomorphize(main_func_id, &context.def_interner);
        assert!(format!("{}", program) == expected);
    }

    #[test]
    fn simple_closure_with_no_captured_variables() {
        let src = r#"
        fn main() -> pub Field {
            let x = 1;
            let closure = || x;
            closure()
        }
        "#;

        let expected_rewrite = r#"fn main$f0() -> Field {
    let x$0 = 1;
    let closure$3 = {
        let closure_variable$2 = {
            let env$1 = (x$l0);
            (env$l1, lambda$f1)
        };
        closure_variable$l2
    };
    {
        let tmp$4 = closure$l3;
        tmp$l4.1(tmp$l4.0)
    }
}
fn lambda$f1(mut env$l1: (Field)) -> Field {
    env$l1.0
}
"#;
        check_rewrite(src, expected_rewrite);
    }
}
