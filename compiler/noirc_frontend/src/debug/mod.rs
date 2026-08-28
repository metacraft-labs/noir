use crate::ast::{PathKind, PathSegment};
use crate::parser::{ParsedModule, ParsedSubModule};
use crate::token::FunctionAttributeKind;
use crate::{ast, ast::Path, parser::ItemKind};
use noirc_artifacts::debug::{DebugFnId, DebugFunction};
use noirc_errors::{Located, Location, Span};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::mem::take;

const MAX_MEMBER_ASSIGN_DEPTH: usize = 8;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SourceVarId(pub u32);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SourceFieldId(pub u32);

/// This structure is used to collect information about variables to track
/// for debugging during the instrumentation injection phase.
#[derive(Debug, Clone)]
pub struct DebugInstrumenter {
    // all collected variable names while instrumenting the source for variable tracking
    pub variables: HashMap<SourceVarId, String>,

    // all field names referenced when assigning to a member of a variable
    pub field_names: HashMap<SourceFieldId, String>,

    // all collected function metadata (name + argument names)
    pub functions: HashMap<DebugFnId, DebugFunction>,

    next_var_id: u32,
    next_field_name_id: u32,
    next_fn_id: u32,

    // last seen variable names and their IDs grouped by scope
    scope: Vec<HashMap<String, SourceVarId>>,
}

impl Default for DebugInstrumenter {
    fn default() -> Self {
        Self {
            variables: HashMap::default(),
            field_names: HashMap::default(),
            functions: HashMap::default(),
            scope: vec![],
            next_var_id: 0,
            next_field_name_id: 1,
            next_fn_id: 0,
        }
    }
}

impl DebugInstrumenter {
    pub fn instrument_module(&mut self, module: &mut ParsedModule) {
        module.items.iter_mut().for_each(|item| {
            match &mut item.kind {
                // Instrument top-level functions of a module
                ItemKind::Function(f) => self.walk_fn(&mut f.def),
                // Instrument contract module
                ItemKind::Submodules(ParsedSubModule {
                    is_contract: true,
                    contents: contract_module,
                    ..
                }) => {
                    self.instrument_module(contract_module);
                }
                _ => (),
            }
        });
    }

    fn insert_var(&mut self, var_name: &str) -> Option<SourceVarId> {
        if var_name == "_" {
            return None;
        }

        let var_id = SourceVarId(self.next_var_id);
        self.next_var_id += 1;
        self.variables.insert(var_id, var_name.to_string());
        self.scope.last_mut().unwrap().insert(var_name.to_string(), var_id);
        Some(var_id)
    }

    fn lookup_var(&self, var_name: &str) -> Option<SourceVarId> {
        self.scope.iter().rev().find_map(|vars| vars.get(var_name).copied())
    }

    fn insert_field_name(&mut self, field_name: &str) -> SourceFieldId {
        let field_name_id = SourceFieldId(self.next_field_name_id);
        self.next_field_name_id += 1;
        self.field_names.insert(field_name_id, field_name.to_string());
        field_name_id
    }

    fn insert_function(&mut self, fn_name: String, arguments: Vec<String>) -> DebugFnId {
        let fn_id = DebugFnId(self.next_fn_id);
        self.next_fn_id += 1;
        self.functions.insert(fn_id, DebugFunction { name: fn_name, arg_names: arguments });
        fn_id
    }

    fn walk_fn(&mut self, func: &mut ast::FunctionDefinition) {
        // Don't instrument functions that are not supposed to have a body
        if let Some((func, _)) = &func.attributes.function {
            match func.kind {
                FunctionAttributeKind::Foreign(_)
                | FunctionAttributeKind::Builtin(_)
                | FunctionAttributeKind::Oracle(_) => return,
                FunctionAttributeKind::Test(..)
                | FunctionAttributeKind::Fold
                | FunctionAttributeKind::NoPredicates
                | FunctionAttributeKind::InlineAlways
                | FunctionAttributeKind::InlineNever
                | FunctionAttributeKind::FuzzingHarness(..) => (),
            }
        }

        let func_name = func.name.to_string();
        let func_args =
            func.parameters.iter().map(|param| pattern_to_string(&param.pattern)).collect();
        let fn_id = self.insert_function(func_name, func_args);
        let enter_stmt = build_debug_call_stmt("enter", fn_id, func.location);
        self.scope.push(HashMap::default());

        let set_fn_params: Vec<_> = func
            .parameters
            .iter()
            .flat_map(|param| {
                pattern_vars(&param.pattern)
                    .iter()
                    .filter_map(|(id, _is_mut)| {
                        let var_id = self.insert_var(id.as_str())?;
                        Some(build_assign_var_stmt(var_id, id_expr(id)))
                    })
                    .collect::<Vec<_>>()
            })
            .collect();

        let func_body = &mut func.body.statements;
        let mut statements = take(func_body);

        self.walk_scope(&mut statements, func.location, true);

        // walk_scope ensures that the last statement is the return value of the function
        let last_stmt = statements.pop().expect("at least one statement after walk_scope");
        let exit_stmt = build_debug_call_stmt("exit", fn_id, last_stmt.location);

        // rebuild function body
        func_body.push(enter_stmt);
        func_body.extend(set_fn_params);
        func_body.extend(statements);
        func_body.push(exit_stmt);
        func_body.push(last_stmt);
    }

    // Modify a vector of statements in-place, adding instrumentation for sets and drops.
    // This function will consume a scope level.
    fn walk_scope(
        &mut self,
        statements: &mut Vec<ast::Statement>,
        location: Location,
        is_function_scope: bool,
    ) {
        statements.iter_mut().for_each(|stmt| self.walk_statement(stmt));

        let temp_var_name = if is_function_scope { "__debug_return_expr" } else { "__debug_expr" };

        let span = Span::empty(location.span.end());
        let location = Location::new(span, location.file);

        // extract and save the return value from the scope if there is one
        let ret_stmt = statements.pop();
        let has_ret_expr = match ret_stmt {
            None => false,
            Some(ast::Statement { kind: ast::StatementKind::Expression(ret_expr), .. }) => {
                let mut save_ret_expr = ast::Statement {
                    kind: ast::StatementKind::new_let(
                        ast::Pattern::Identifier(ident(temp_var_name, location)),
                        None,
                        ret_expr.clone(),
                        vec![],
                    ),
                    location,
                };
                if is_function_scope {
                    // call walk_statement on the new let statement, in order to make the return variable visible in the debugger
                    self.walk_statement(&mut save_ret_expr);
                }
                statements.push(save_ret_expr);
                true
            }
            Some(ret_stmt) => {
                // not an expression, so leave it untouched
                statements.push(ret_stmt);
                false
            }
        };

        // drop scope variables
        let scope_vars = self.scope.pop().unwrap_or_default();
        let drop_vars_stmts =
            scope_vars.values().map(|var_id| build_drop_var_stmt(*var_id, location));
        statements.extend(drop_vars_stmts);

        // return the saved value in temp_var_name, or unit otherwise
        let last_stmt = if has_ret_expr {
            ast::Statement {
                kind: ast::StatementKind::Expression(ast::Expression {
                    kind: ast::ExpressionKind::Variable(Path::plain(
                        vec![PathSegment::from(ident(temp_var_name, location))],
                        location,
                    )),
                    location,
                }),
                location,
            }
        } else {
            ast::Statement {
                kind: ast::StatementKind::Expression(ast::Expression {
                    kind: ast::ExpressionKind::Literal(ast::Literal::Unit),
                    location,
                }),
                location,
            }
        };
        statements.push(last_stmt);
    }

    fn walk_let_statement(
        &mut self,
        let_stmt: &ast::LetStatement,
        location: Location,
    ) -> ast::Statement {
        // rewrites let statements written like this:
        //   let (((a,b,c),D { d }),e,f) = x;
        //
        // into statements like this:
        //
        //   let (a,b,c,d,e,f,g) = {
        //     let (((a,b,c),D { d }),e,f) = x;
        //     wrap(1, a);
        //     wrap(2, b);
        //     ...
        //     wrap(6, f);
        //     (a,b,c,d,e,f,g)
        //   };

        // a.b.c[3].x[i*4+1].z

        let vars = pattern_vars(&let_stmt.pattern);
        let vars_pattern: Vec<ast::Pattern> = vars
            .iter()
            .map(|(id, is_mut)| {
                if *is_mut {
                    ast::Pattern::Mutable(
                        Box::new(ast::Pattern::Identifier(id.clone())),
                        id.location(),
                        true,
                    )
                } else {
                    ast::Pattern::Identifier(id.clone())
                }
            })
            .collect();
        let vars_exprs: Vec<ast::Expression> = vars
            .iter()
            .map(|(id, _)| {
                // We don't want to generate an expression to read from "_".
                // And since this expression is going to be assigned to "_" so it doesn't matter
                // what it is, we can use `()` for it.
                if id.as_str() == "_" {
                    ast::Expression {
                        kind: ast::ExpressionKind::Literal(ast::Literal::Unit),
                        location: id.location(),
                    }
                } else {
                    id_expr(id)
                }
            })
            .collect();

        let mut block_stmts =
            vec![ast::Statement { kind: ast::StatementKind::Let(let_stmt.clone()), location }];
        block_stmts.extend(vars.iter().filter_map(|(id, _)| {
            let var_id = self.insert_var(id.as_str())?;
            Some(build_assign_var_stmt(var_id, id_expr(id)))
        }));
        block_stmts.push(ast::Statement {
            kind: ast::StatementKind::Expression(ast::Expression {
                kind: ast::ExpressionKind::Tuple(vars_exprs),
                location: let_stmt.pattern.location(),
            }),
            location: let_stmt.pattern.location(),
        });

        ast::Statement {
            kind: ast::StatementKind::new_let(
                ast::Pattern::Tuple(vars_pattern, let_stmt.pattern.location()),
                None,
                ast::Expression {
                    kind: ast::ExpressionKind::Block(ast::BlockExpression {
                        statements: block_stmts,
                    }),
                    location: let_stmt.expression.location,
                },
                vec![],
            ),
            location,
        }
    }

    /// Instrument a compound assignment (`x += y`, `p.x *= y`, …).
    ///
    /// The parser used to desugar `x <op>= y` into `x = x <op> y` itself, so
    /// [`Self::walk_assign_statement`] saw every compound assignment as an
    /// [`ast::StatementKind::Assign`] and emitted the `__debug_var_assign`
    /// call that keeps the debugger's view of the variable current. `AssignOp`
    /// is now its own statement kind, desugared later in the elaborator, and
    /// this pass had no arm for it — so compound assignments stopped being
    /// instrumented at all and every variable updated with `+=`/`*=`/… kept
    /// its previous value in the debugger and in recorded traces, silently.
    ///
    /// Two things this desugaring must preserve, both pinned by
    /// `test_programs/execution_success/op_assign_desugaring`:
    ///
    /// * **the right-hand side is evaluated before the lvalue is read**, so
    ///   `i += { i = 10; 1 }` yields 11 and not 1. The rhs is therefore bound
    ///   to a temporary first, exactly as `Elaborator::elaborate_assign_op`
    ///   does;
    /// * **an lvalue index sub-expression is evaluated exactly once**, so
    ///   `x[{ x[0] += 2; 0 }] += 3` runs its index block once. Reading the
    ///   lvalue back a second time is what would break this, and it cannot be
    ///   avoided at this stage: the elaborator reuses the *elaborated* lvalue,
    ///   which does not exist yet here. So compound assignments through an
    ///   [`ast::LValue::Index`] are left uninstrumented — the assignment still
    ///   happens, the debugger just does not observe it. `Path` and
    ///   `MemberAccess` lvalues have no sub-expressions to re-evaluate and are
    ///   instrumented normally, which covers `x += 1` and `p.x += 1`.
    fn walk_assign_op_statement(
        &mut self,
        assign_op_stmt: &ast::AssignOpStatement,
        location: Location,
    ) -> Option<ast::Statement> {
        if lvalue_has_index(&assign_op_stmt.lvalue) {
            return None;
        }

        let operator_location = assign_op_stmt.op.location();
        let expression_location = assign_op_stmt.expression.location;
        let rhs_ident = ident("__debug_op_rhs", expression_location);

        // `<rhs>` is bound before the lvalue is read, so any side effect it has
        // is observed by the lvalue.
        let bind_rhs = ast::Statement {
            kind: ast::StatementKind::new_let(
                ast::Pattern::Identifier(rhs_ident.clone()),
                None,
                assign_op_stmt.expression.clone(),
                vec![],
            ),
            location: expression_location,
        };
        let apply_op = ast::Statement {
            kind: ast::StatementKind::Expression(ast::Expression {
                kind: ast::ExpressionKind::Infix(Box::new(ast::InfixExpression {
                    lhs: assign_op_stmt.lvalue.as_expression(),
                    operator: Located::from(
                        operator_location,
                        assign_op_stmt.op.contents.to_binary_op_kind(),
                    ),
                    rhs: id_expr(&rhs_ident),
                })),
                location: expression_location,
            }),
            location: expression_location,
        };

        let desugared = ast::AssignStatement {
            lvalue: assign_op_stmt.lvalue.clone(),
            expression: ast::Expression {
                kind: ast::ExpressionKind::Block(ast::BlockExpression {
                    statements: vec![bind_rhs, apply_op],
                }),
                location: expression_location,
            },
        };

        Some(self.walk_assign_statement(&desugared, location))
    }

    fn walk_assign_statement(
        &mut self,
        assign_stmt: &ast::AssignStatement,
        location: Location,
    ) -> ast::Statement {
        // X = Y becomes:
        // X = {
        //   let __debug_expr = Y;
        //
        //   __debug_var_assign(17, __debug_expr);
        //   // or:
        //   __debug_member_assign_{arity}(17, __debug_expr, _v0, _v1..., _v{arity});
        //
        //   __debug_expr
        // };

        let let_kind = ast::StatementKind::new_let(
            ast::Pattern::Identifier(ident("__debug_expr", assign_stmt.expression.location)),
            None,
            assign_stmt.expression.clone(),
            vec![],
        );
        let expression_location = assign_stmt.expression.location;
        let new_assign_stmt = match &assign_stmt.lvalue {
            ast::LValue::Path(id) => {
                let Some(id) = id.as_ident() else {
                    panic!("var lookup failed for var_name={id}");
                };
                let var_id = self
                    .lookup_var(id.as_str())
                    .unwrap_or_else(|| panic!("var lookup failed for var_name={id}"));
                build_assign_var_stmt(var_id, id_expr(&ident("__debug_expr", id.location())))
            }
            ast::LValue::Dereference(_lv, location) => {
                // TODO: this is a dummy statement for now, but we should
                // somehow track the dereference and update the pointed to
                // variable
                ast::Statement {
                    kind: ast::StatementKind::Expression(uint_expr(0, *location)),
                    location: *location,
                }
            }
            // `x[i] = v`, `p.field = v`, and interned lvalues, all of which are
            // recorded as a member assignment against the root variable. Spelled
            // out rather than left as `_` so that a new `LValue` variant is a
            // compile error here too — the inner walk below is already
            // exhaustive, and this arm is what feeds it.
            ast::LValue::MemberAccess { .. }
            | ast::LValue::Index { .. }
            | ast::LValue::Interned(..) => {
                let mut indexes = vec![];
                let mut cursor = &assign_stmt.lvalue;
                let var_id;
                loop {
                    match cursor {
                        ast::LValue::Path(id) => {
                            let Some(id) = id.as_ident() else {
                                panic!("var lookup failed for var_name={id}");
                            };

                            var_id = self
                                .lookup_var(id.as_str())
                                .unwrap_or_else(|| panic!("var lookup failed for var_name={id}"));
                            break;
                        }
                        ast::LValue::MemberAccess { object, field_name, location } => {
                            cursor = object;
                            let field_name_id = self.insert_field_name(field_name.as_str());
                            indexes.push(sint_expr(-i128::from(field_name_id.0), *location));
                        }
                        ast::LValue::Index { index, array, location: _ } => {
                            cursor = array;
                            indexes.push(index.clone());
                        }
                        ast::LValue::Dereference(_ref, _span) => {
                            unimplemented![]
                        }
                        ast::LValue::Interned(..) => {
                            unimplemented![]
                        }
                    }
                }
                build_assign_member_stmt(
                    var_id,
                    &indexes,
                    &id_expr(&ident("__debug_expr", expression_location)),
                )
            }
        };

        let ret_kind =
            ast::StatementKind::Expression(id_expr(&ident("__debug_expr", expression_location)));

        ast::Statement {
            kind: ast::StatementKind::Assign(ast::AssignStatement {
                lvalue: assign_stmt.lvalue.clone(),
                expression: ast::Expression {
                    kind: ast::ExpressionKind::Block(ast::BlockExpression {
                        statements: vec![
                            ast::Statement { kind: let_kind, location: expression_location },
                            new_assign_stmt,
                            ast::Statement { kind: ret_kind, location: expression_location },
                        ],
                    }),
                    location: expression_location,
                },
            }),
            location,
        }
    }

    fn walk_expr(&mut self, expr: &mut ast::Expression) {
        match &mut expr.kind {
            ast::ExpressionKind::Block(ast::BlockExpression { statements, .. }) => {
                self.scope.push(HashMap::default());
                self.walk_scope(statements, expr.location, false);
            }
            ast::ExpressionKind::Prefix(prefix_expr) => {
                self.walk_expr(&mut prefix_expr.rhs);
            }
            ast::ExpressionKind::Index(index_expr) => {
                self.walk_expr(&mut index_expr.collection);
                self.walk_expr(&mut index_expr.index);
            }
            ast::ExpressionKind::Call(call_expr) => {
                // TODO: push a stack frame or something here?
                self.walk_expr(&mut call_expr.func);
                call_expr.arguments.iter_mut().for_each(|expr| {
                    self.walk_expr(expr);
                });
            }
            ast::ExpressionKind::MethodCall(mc_expr) => {
                // TODO: also push a stack frame here
                self.walk_expr(&mut mc_expr.object);
                mc_expr.arguments.iter_mut().for_each(|expr| {
                    self.walk_expr(expr);
                });
            }
            ast::ExpressionKind::Constructor(c_expr) => {
                c_expr.fields.iter_mut().for_each(|(_id, expr)| {
                    self.walk_expr(expr);
                });
            }
            ast::ExpressionKind::MemberAccess(ma_expr) => {
                self.walk_expr(&mut ma_expr.lhs);
            }
            ast::ExpressionKind::Cast(cast_expr) => {
                self.walk_expr(&mut cast_expr.lhs);
            }
            ast::ExpressionKind::Infix(infix_expr) => {
                self.walk_expr(&mut infix_expr.lhs);
                self.walk_expr(&mut infix_expr.rhs);
            }
            ast::ExpressionKind::If(if_expr) => {
                self.walk_expr(&mut if_expr.condition);
                self.walk_expr(&mut if_expr.consequence);
                if let Some(ref mut alt) = if_expr.alternative {
                    self.walk_expr(alt);
                }
            }
            ast::ExpressionKind::Tuple(exprs) => {
                exprs.iter_mut().for_each(|ref mut expr| {
                    self.walk_expr(expr);
                });
            }
            ast::ExpressionKind::Lambda(lambda) => {
                self.walk_expr(&mut lambda.body);
            }
            ast::ExpressionKind::Parenthesized(expr) => {
                self.walk_expr(expr);
            }

            // ----------------------------------------------------------------
            // Everything below is deliberately NOT descended into. The match is
            // exhaustive on purpose: `ExpressionKind` is an upstream enum, and a
            // catch-all here is a drift hazard. When upstream adds a variant the
            // tracer must decide about, this file must stop compiling rather
            // than silently stop recording. (`StatementKind::AssignOp` is the
            // worked example — see `walk_assign_op_statement` and the tests at
            // the bottom of this file.)
            // ----------------------------------------------------------------

            // Leaves with no sub-expressions to walk.
            ast::ExpressionKind::Variable(_)
            | ast::ExpressionKind::AsTraitPath(_)
            | ast::ExpressionKind::TypePath(_)
            | ast::ExpressionKind::Error => {}

            // `Literal::Array`/`Slice`/`FmtStr` do carry sub-expressions, but the
            // instrumenter has never descended into them and doing so now would
            // change every recorded trace containing an array literal. Left as a
            // known gap rather than an accidental one.
            ast::ExpressionKind::Literal(_) => {}

            // `constrain`/`assert` operands are pure checks: they cannot assign,
            // so there is no `__debug_var_assign` to emit inside them.
            ast::ExpressionKind::Constrain(_) => {}

            // Comptime code runs in the interpreter, not in the traced program,
            // so instrumentation calls placed inside it would never be observed.
            ast::ExpressionKind::Comptime(..)
            | ast::ExpressionKind::Quote(_)
            | ast::ExpressionKind::Unquote(_) => {}

            // Already-elaborated or interned nodes: the AST this pass edits is
            // no longer the representation these carry.
            ast::ExpressionKind::Resolved(_)
            | ast::ExpressionKind::Interned(_)
            | ast::ExpressionKind::InternedStatement(_) => {}

            // Known gaps, listed so they are visible rather than silent:
            // `match` arms and `unsafe { .. }` bodies are not instrumented, so
            // assignments inside them are not recorded.
            ast::ExpressionKind::Match(_) | ast::ExpressionKind::Unsafe(_) => {}
        }
    }

    fn walk_for(&mut self, for_stmt: &mut ast::ForLoopStatement) {
        let var_name = for_stmt.identifier.as_str();
        let var_id = self.insert_var(var_name);

        let set_and_drop_stmt = var_id.map(|var_id| {
            let span = Span::empty(for_stmt.location.span.end());
            (
                build_assign_var_stmt(var_id, id_expr(&for_stmt.identifier)),
                build_drop_var_stmt(var_id, Location::new(span, for_stmt.location.file)),
            )
        });

        self.walk_expr(&mut for_stmt.block);

        let mut statements = Vec::new();
        let block_statement = ast::Statement {
            kind: ast::StatementKind::Semi(for_stmt.block.clone()),
            location: for_stmt.block.location,
        };

        if let Some((set_stmt, drop_stmt)) = set_and_drop_stmt {
            statements.push(set_stmt);
            statements.push(block_statement);
            statements.push(drop_stmt);
        } else {
            statements.push(block_statement);
        }

        for_stmt.block = ast::Expression {
            kind: ast::ExpressionKind::Block(ast::BlockExpression { statements }),
            location: for_stmt.location,
        };
    }

    fn walk_statement(&mut self, stmt: &mut ast::Statement) {
        match &mut stmt.kind {
            ast::StatementKind::Let(let_stmt) => {
                *stmt = self.walk_let_statement(let_stmt, stmt.location);
            }
            ast::StatementKind::Assign(assign_stmt) => {
                *stmt = self.walk_assign_statement(assign_stmt, stmt.location);
            }
            ast::StatementKind::AssignOp(assign_op_stmt) => {
                if let Some(instrumented) =
                    self.walk_assign_op_statement(assign_op_stmt, stmt.location)
                {
                    *stmt = instrumented;
                }
            }
            ast::StatementKind::Expression(expr) => {
                self.walk_expr(expr);
            }
            ast::StatementKind::Semi(expr) => {
                self.walk_expr(expr);
            }
            ast::StatementKind::For(for_stmt) => {
                self.walk_for(for_stmt);
            }
            ast::StatementKind::Loop(loop_stmt) => {
                self.walk_expr(&mut loop_stmt.body);
            }
            ast::StatementKind::While(while_stmt) => {
                self.walk_expr(&mut while_stmt.condition);
                self.walk_expr(&mut while_stmt.body);
            }

            // ----------------------------------------------------------------
            // This match used to end in `_ => {} // Constrain, Error` — a
            // catch-all whose comment enumerated what its author expected to
            // reach it. `StatementKind` is an *upstream* enum: when
            // noir-lang/noir#12123 made `x <op>= y` its own `AssignOp` variant
            // instead of desugaring it in the parser, that variant joined the
            // catch-all silently, and every compound assignment stopped being
            // recorded while the program still computed the right answer. A
            // green build, a passing test suite, and a wrong trace.
            //
            // The match is therefore exhaustive on purpose. A new upstream
            // variant must break this build, and whoever fixes it must decide
            // in writing whether the tracer records it. Do not reintroduce a
            // catch-all here.
            // ----------------------------------------------------------------

            // Control-flow markers: nothing to record and nothing to descend
            // into.
            ast::StatementKind::Break | ast::StatementKind::Continue => {}

            // Runs in the comptime interpreter, not in the traced program, so
            // instrumentation placed inside it would never be observed.
            ast::StatementKind::Comptime(_) => {}

            // The real `StatementKind` lives in the `NodeInterner`; this pass
            // edits the parsed AST and cannot reach it.
            ast::StatementKind::Interned(_) => {}

            // A recovered parse error. Compilation is already failing.
            ast::StatementKind::Error => {}
        }
    }
}

pub fn build_debug_crate_file() -> String {
    [
        r#"
            #[oracle(__debug_var_assign)]
            unconstrained fn __debug_var_assign_oracle<T>(_var_id: u32, _value: T) {}
            unconstrained fn __debug_var_assign_inner<T>(var_id: u32, value: T) {
                __debug_var_assign_oracle(var_id, value);
            }
            pub fn __debug_var_assign<T>(var_id: u32, value: T) {
                // Safety: debug context
                unsafe {
                {
                    __debug_var_assign_inner(var_id, value);
                }}
            }

            #[oracle(__debug_var_drop)]
            unconstrained fn __debug_var_drop_oracle(_var_id: u32) {}
            unconstrained fn __debug_var_drop_inner(var_id: u32) {
                __debug_var_drop_oracle(var_id);
            }
            pub fn __debug_var_drop(var_id: u32) {
                // Safety: debug context
                unsafe {
                {
                    __debug_var_drop_inner(var_id);
                }}
            }

            #[oracle(__debug_fn_enter)]
            unconstrained fn __debug_fn_enter_oracle(_fn_id: u32) {}
            unconstrained fn __debug_fn_enter_inner(fn_id: u32) {
                __debug_fn_enter_oracle(fn_id);
            }
            pub fn __debug_fn_enter(fn_id: u32) {
                // Safety: debug context
                unsafe {
                {
                    __debug_fn_enter_inner(fn_id);
                }}
            }

            #[oracle(__debug_fn_exit)]
            unconstrained fn __debug_fn_exit_oracle(_fn_id: u32) {}
            unconstrained fn __debug_fn_exit_inner(fn_id: u32) {
                __debug_fn_exit_oracle(fn_id);
            }
            pub fn __debug_fn_exit(fn_id: u32) {
                // Safety: debug context
                unsafe {
                {
                    __debug_fn_exit_inner(fn_id);
                }}
            }

            #[oracle(__debug_dereference_assign)]
            unconstrained fn __debug_dereference_assign_oracle<T>(_var_id: u32, _value: T) {}
            unconstrained fn __debug_dereference_assign_inner<T>(var_id: u32, value: T) {
                __debug_dereference_assign_oracle(var_id, value);
            }
            pub fn __debug_dereference_assign<T>(var_id: u32, value: T) {
                // Safety: debug context
                unsafe {
                {
                    __debug_dereference_assign_inner(var_id, value);
                }}
            }
        "#
        .to_string(),
        (1..=MAX_MEMBER_ASSIGN_DEPTH)
            .map(|n| {
                // The variable signature has to be generic as Noir supports using any polymorphic integer as an index.
                // If we were to set a specific type for index signatures here, such as `Field`, we will error in
                // type checking if we attempt to index with a different type such as `u8`.
                let indices =
                    (0..n).map(|i| format!["Index{i}"]).collect::<Vec<String>>().join(", ");
                let var_sig =
                    (0..n).map(|i| format!["_v{i}: Index{i}"]).collect::<Vec<String>>().join(", ");
                let vars = (0..n).map(|i| format!["_v{i}"]).collect::<Vec<String>>().join(", ");
                format!(
                    r#"
                #[oracle(__debug_member_assign_{n})]
                unconstrained fn __debug_oracle_member_assign_{n}<T, {indices}>(
                    _var_id: u32, _value: T, {var_sig}
                ) {{}}
                unconstrained fn __debug_inner_member_assign_{n}<T, {indices}>(
                    var_id: u32, value: T, {var_sig}
                ) {{
                    __debug_oracle_member_assign_{n}(var_id, value, {vars});
                }}
                pub fn __debug_member_assign_{n}<T, {indices}>(var_id: u32, value: T, {var_sig}) {{
                    /// Safety: debug context
                    unsafe {{
                        __debug_inner_member_assign_{n}(var_id, value, {vars});
                    }}
                }}

            "#
                )
            })
            .collect::<Vec<String>>()
            .join("\n"),
    ]
    .join("\n")
}

/// Build a fully-qualified path `::__debug::{name}` so that debug function calls
/// bypass any user-defined modules or functions with conflicting names.
fn debug_fn_path(name: &str, location: Location) -> Path {
    Path {
        segments: vec![
            PathSegment::from(ident("__debug", location)),
            PathSegment::from(ident(name, location)),
        ],
        kind: PathKind::Absolute,
        location,
        kind_location: location,
    }
}

fn build_assign_var_stmt(var_id: SourceVarId, expr: ast::Expression) -> ast::Statement {
    let location = expr.location;
    let kind = ast::ExpressionKind::Call(Box::new(ast::CallExpression {
        func: Box::new(ast::Expression {
            kind: ast::ExpressionKind::Variable(debug_fn_path("__debug_var_assign", location)),
            location,
        }),
        is_macro_call: false,
        arguments: vec![uint_expr(u128::from(var_id.0), location), expr],
    }));
    ast::Statement { kind: ast::StatementKind::Semi(ast::Expression { kind, location }), location }
}

fn build_drop_var_stmt(var_id: SourceVarId, location: Location) -> ast::Statement {
    let kind = ast::ExpressionKind::Call(Box::new(ast::CallExpression {
        func: Box::new(ast::Expression {
            kind: ast::ExpressionKind::Variable(debug_fn_path("__debug_var_drop", location)),
            location,
        }),
        is_macro_call: false,
        arguments: vec![uint_expr(u128::from(var_id.0), location)],
    }));
    ast::Statement { kind: ast::StatementKind::Semi(ast::Expression { kind, location }), location }
}

fn build_assign_member_stmt(
    var_id: SourceVarId,
    indexes: &[ast::Expression],
    expr: &ast::Expression,
) -> ast::Statement {
    let arity = indexes.len();
    if arity > MAX_MEMBER_ASSIGN_DEPTH {
        unreachable!("Assignment to member exceeds maximum depth for debugging");
    }
    let location = expr.location;
    let kind = ast::ExpressionKind::Call(Box::new(ast::CallExpression {
        func: Box::new(ast::Expression {
            kind: ast::ExpressionKind::Variable(debug_fn_path(
                &format!["__debug_member_assign_{arity}"],
                location,
            )),
            location,
        }),
        is_macro_call: false,
        arguments: [
            vec![uint_expr(u128::from(var_id.0), location)],
            vec![expr.clone()],
            indexes.iter().rev().cloned().collect(),
        ]
        .concat(),
    }));
    ast::Statement { kind: ast::StatementKind::Semi(ast::Expression { kind, location }), location }
}

fn build_debug_call_stmt(fname: &str, fn_id: DebugFnId, location: Location) -> ast::Statement {
    let kind = ast::ExpressionKind::Call(Box::new(ast::CallExpression {
        func: Box::new(ast::Expression {
            kind: ast::ExpressionKind::Variable(debug_fn_path(
                &format!["__debug_fn_{fname}"],
                location,
            )),
            location,
        }),
        is_macro_call: false,
        arguments: vec![uint_expr(u128::from(fn_id.0), location)],
    }));
    ast::Statement { kind: ast::StatementKind::Semi(ast::Expression { kind, location }), location }
}

/// Whether an lvalue reaches its target through an index expression, which
/// cannot be re-evaluated safely. See [`DebugInstrumenter::walk_assign_op_statement`].
fn lvalue_has_index(lvalue: &ast::LValue) -> bool {
    match lvalue {
        ast::LValue::Index { .. } => true,
        ast::LValue::MemberAccess { object, .. } => lvalue_has_index(object),
        ast::LValue::Path(_) => false,
        // A dereference target is an arbitrary expression, and the existing
        // assign instrumentation does not track dereferences anyway.
        ast::LValue::Dereference(..) | ast::LValue::Interned(..) => true,
    }
}

fn pattern_vars(pattern: &ast::Pattern) -> Vec<(ast::Ident, bool)> {
    let mut vars = vec![];
    let mut stack = VecDeque::from([(pattern, false)]);
    while stack.front().is_some() {
        let (pattern, is_mut) = stack.pop_front().unwrap();
        match pattern {
            ast::Pattern::Identifier(id) => {
                if id.as_str() != "_" {
                    vars.push((id.clone(), is_mut));
                }
            }
            ast::Pattern::Mutable(pattern, _, _) => {
                stack.push_back((pattern, true));
            }
            ast::Pattern::Tuple(patterns, _) => {
                stack.extend(patterns.iter().map(|pattern| (pattern, is_mut)));
            }
            ast::Pattern::Struct(_, fields, _) => {
                stack.extend(fields.iter().map(|(_, pattern)| (pattern, is_mut)));
            }
            ast::Pattern::Parenthesized(pattern, _) => {
                stack.push_back((pattern, is_mut));
            }
            ast::Pattern::Interned(_, _) => (),
        }
    }
    vars
}

fn pattern_to_string(pattern: &ast::Pattern) -> String {
    match pattern {
        ast::Pattern::Identifier(id) => id.to_string(),
        ast::Pattern::Mutable(pattern, _, _) => {
            format!("mut {}", pattern_to_string(pattern.as_ref()))
        }
        ast::Pattern::Tuple(elements, _) => format!(
            "({})",
            elements.iter().map(pattern_to_string).collect::<Vec<String>>().join(", ")
        ),
        ast::Pattern::Struct(name, fields, _) => {
            format!(
                "{} {{ {} }}",
                name,
                fields
                    .iter()
                    .map(|(field_ident, field_pattern)| {
                        format!("{}: {}", field_ident, pattern_to_string(field_pattern))
                    })
                    .collect::<Vec<_>>()
                    .join(", "),
            )
        }
        ast::Pattern::Parenthesized(pattern, _) => {
            format!("({})", pattern_to_string(pattern.as_ref()))
        }
        ast::Pattern::Interned(_, _) => "?Interned".to_string(),
    }
}

fn ident(s: &str, location: Location) -> ast::Ident {
    ast::Ident::new(s.to_string(), location)
}

fn id_expr(id: &ast::Ident) -> ast::Expression {
    ast::Expression {
        kind: ast::ExpressionKind::Variable(Path::plain(
            vec![PathSegment::from(id.clone())],
            id.location(),
        )),
        location: id.location(),
    }
}

fn uint_expr(x: u128, location: Location) -> ast::Expression {
    let kind = ast::ExpressionKind::Literal(ast::Literal::Integer(x.into(), None));
    ast::Expression { kind, location }
}

fn sint_expr(x: i128, location: Location) -> ast::Expression {
    let kind = ast::ExpressionKind::Literal(ast::Literal::Integer(x.into(), None));
    ast::Expression { kind, location }
}

#[cfg(test)]
mod tests {
    //! Regression tests for [`DebugInstrumenter`].
    //!
    //! These exist because of a **silent** defect. noir-lang/noir#12123 made
    //! `x <op>= y` its own [`ast::StatementKind::AssignOp`] variant instead of
    //! desugaring it in the parser, and marked the change a bug fix with no
    //! breaking-change flag. [`DebugInstrumenter::walk_statement`] ended in a
    //! `_ => {}` catch-all, so compound assignments simply stopped being
    //! instrumented: the compiled program still computed the right answer, no
    //! test failed, and every `+=`/`*=`/… kept its pre-assignment value in the
    //! debugger and in recorded traces.
    //!
    //! `test_programs/execution_success/op_assign_desugaring` pins the
    //! *evaluation semantics* of the desugaring, but it cannot catch this: the
    //! program executes correctly whether or not the instrumenter touched it.
    //! Only counting the emitted `__debug_var_assign` calls does.

    use super::DebugInstrumenter;
    use crate::parser::parse_program_with_dummy_file;

    /// Instrument `src` and render the resulting module back to source.
    fn instrument(src: &str) -> String {
        let (mut module, errors) = parse_program_with_dummy_file(src);
        assert!(errors.is_empty(), "fixture failed to parse: {errors:?}");
        DebugInstrumenter::default().instrument_module(&mut module);

        module
            .items
            .iter()
            .filter_map(|item| match &item.kind {
                crate::parser::ItemKind::Function(f) => Some(f.to_string()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn count(haystack: &str, needle: &str) -> usize {
        haystack.matches(needle).count()
    }

    /// The defect itself: four compound assignments must produce four
    /// `__debug_var_assign` calls on top of the three entry-time parameter
    /// bindings. Before the `AssignOp` arm existed this was **3** — the
    /// parameters only — and `x` was recorded as `3` for the whole run while
    /// the circuit correctly computed `429981696`.
    ///
    /// This is `test_programs/trace/a_1_mul` reduced to what the instrumenter
    /// can be asked about without building `nargo`.
    #[test]
    fn compound_assignment_emits_a_var_assign_per_statement() {
        let instrumented = instrument(
            "fn main(mut x: u32, y: u32, z: u32) {
                 x *= y;
                 x *= x;
                 x *= x;
                 x *= x;
                 assert(x == z);
             }",
        );

        assert_eq!(
            count(&instrumented, "__debug_var_assign"),
            3 + 4,
            "expected 3 parameter bindings + 1 per compound assignment, got:\n{instrumented}"
        );
    }

    /// The control for the test above: the same program written out longhand
    /// has always been instrumented, and must stay identical in count. If this
    /// one ever disagrees with the compound-assignment count, the desugaring
    /// has drifted rather than the arm having gone missing.
    #[test]
    fn compound_and_longhand_assignment_agree() {
        let compound = instrument(
            "fn main(mut x: u32, y: u32) {
                 x *= y;
             }",
        );
        let longhand = instrument(
            "fn main(mut x: u32, y: u32) {
                 x = x * y;
             }",
        );

        assert_eq!(
            count(&compound, "__debug_var_assign"),
            count(&longhand, "__debug_var_assign"),
            "`x *= y` and `x = x * y` must be recorded the same number of times\
             \ncompound:\n{compound}\nlonghand:\n{longhand}"
        );
    }

    /// The right-hand side is bound to a temporary *before* the lvalue is read,
    /// so a side-effecting rhs is observed by the lvalue
    /// (`i += { i = 10; 1 }` is 11, not 1). This pins the shape of the
    /// desugaring, not just its count.
    #[test]
    fn compound_assignment_binds_the_rhs_before_reading_the_lvalue() {
        let instrumented = instrument(
            "fn main(mut x: u32, y: u32) {
                 x += y;
             }",
        );

        let bound = instrumented.find("let __debug_op_rhs").unwrap_or_else(|| {
            panic!("the rhs must be bound to a temporary, got:\n{instrumented}")
        });
        let lvalue_read = instrumented.find("(x + __debug_op_rhs)").unwrap_or_else(|| {
            panic!("the operator must be applied to the bound temporary, got:\n{instrumented}")
        });
        assert!(
            bound < lvalue_read,
            "the rhs temporary must be bound before the lvalue is read:\n{instrumented}"
        );
    }

    /// `p.x += 1` goes through the member-assignment oracle, like `p.x = ...`.
    #[test]
    fn compound_assignment_to_a_member_is_instrumented() {
        let instrumented = instrument(
            "fn main() {
                 let mut p = Pair { x: 1, y: 2 };
                 p.x += 5;
             }",
        );

        assert_eq!(
            count(&instrumented, "__debug_member_assign_1"),
            1,
            "expected one member assignment to be recorded, got:\n{instrumented}"
        );
    }

    /// A deliberate, documented gap rather than an accident: instrumenting
    /// `x[expr] += v` at this stage would re-evaluate `expr`, and
    /// `test_programs/execution_success/op_assign_desugaring` pins that it must
    /// run exactly once. The assignment still happens; the debugger just does
    /// not observe it. Asserted so that a future fix has to update this test
    /// rather than change recorded traces silently.
    #[test]
    fn compound_assignment_through_an_index_is_left_uninstrumented() {
        let instrumented = instrument(
            "fn main() {
                 let mut xs = [1, 2, 3];
                 xs[0] += 3;
             }",
        );

        assert_eq!(
            count(&instrumented, "__debug_member_assign"),
            0,
            "indexed compound assignment must not be instrumented, got:\n{instrumented}"
        );
    }

    /// `while` and `loop` bodies reached the same `_ => {}` catch-all that hid
    /// the `AssignOp` defect, so assignments inside them were never recorded.
    /// Now that [`DebugInstrumenter::walk_statement`] is exhaustive they are
    /// walked like a `for` body.
    #[test]
    fn while_and_loop_bodies_are_instrumented() {
        let while_loop = instrument(
            "unconstrained fn main(mut x: u32) {
                 while x < 10 {
                     x += 1;
                 }
             }",
        );
        assert_eq!(
            count(&while_loop, "__debug_var_assign"),
            1 + 1,
            "expected the parameter binding plus the assignment in the loop body, got:\n{while_loop}"
        );

        let bare_loop = instrument(
            "unconstrained fn main(mut x: u32) {
                 loop {
                     x += 1;
                 }
             }",
        );
        assert_eq!(
            count(&bare_loop, "__debug_var_assign"),
            1 + 1,
            "expected the parameter binding plus the assignment in the loop body, got:\n{bare_loop}"
        );
    }
}
