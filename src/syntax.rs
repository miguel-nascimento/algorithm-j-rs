use std::{collections::HashMap, fmt::Display};

use crate::hm::{Env, Type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Unit value
    /// `()`
    Unit,
    /// Identifier
    /// `x`
    Identifier(String),
    /// Int values
    /// `123`
    Int(i32),
    /// Lambda abstraction
    /// `\x -> e`
    Lambda(String, Box<Expr>),
    /// Function application
    /// `f e`
    Apply(Box<Expr>, Box<Expr>),
    /// Let binding
    /// `let f = e1 in e2`
    Let(String, Box<Expr>, Box<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn should_parenthesize(expr: &Expr) -> bool {
            matches!(expr, Expr::Apply(_, _))
        }

        match self {
            Expr::Unit => write!(f, "()"),
            Expr::Identifier(id) => write!(f, "{id}"),
            Expr::Int(int) => write!(f, "{}", int),
            Expr::Lambda(x, body) => write!(f, "fun {} -> {}", x, body),
            Expr::Apply(e1, e2) => {
                if should_parenthesize(e1) {
                    write!(f, "({}) {}", e1, e2)
                } else {
                    write!(f, "{} {}", e1, e2)
                }
            }
            Expr::Let(x, e1, e2) => write!(f, "let {} = {} in {}", x, e1, e2),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stmt {
    Def(String, Expr),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Def(name, expr) => write!(f, "let {} = {};", name, expr),
        }
    }
}

impl Stmt {
    pub fn type_of(&self, env: &mut Env) -> anyhow::Result<Type> {
        match self {
            Stmt::Def(_, expr) => env.infer(expr.clone()),
        }
    }
    pub fn get_name(&self) -> String {
        match self {
            Stmt::Def(name, _) => name.clone(),
        }
    }
    pub fn get_expr(&self) -> Expr {
        match self {
            Stmt::Def(_, expr) => expr.clone(),
        }
    }

    /// Maybe the right way would be include the let? Like the following
    /// Input:
    /// ```no_run
    /// let id = fun x -> x;
    /// let unit_id = id ();
    /// ```
    /// Output
    /// ```no_run
    /// let unit_id =
    ///     let id = fun x -> x in
    ///     in id ();
    /// ```
    /// Currently, this function inlines the definition
    /// ```no_run
    /// let unit_id = (fun x -> x) x;
    /// ```
    /// But should be fine for now, its a toy project anyway
    pub fn with_inline_def(self, deftable: &mut HashMap<String, Expr>) -> Stmt {
        let Stmt::Def(name, expr) = self;

        let mut new_expr = expr.clone();

        fn with_inline_def_impl(expr: &mut Expr, deftable: &mut HashMap<String, Expr>) {
            match expr {
                Expr::Let(name, box e1, box e2) => {
                    with_inline_def_impl(e1, deftable);
                    deftable.insert(name.clone(), e1.clone());
                    with_inline_def_impl(e2, deftable);
                }
                Expr::Apply(f, body) => {
                    with_inline_def_impl(f, deftable);
                    with_inline_def_impl(body, deftable);
                }
                Expr::Lambda(_, box body) => {
                    with_inline_def_impl(body, deftable);
                }
                Expr::Identifier(name) => {
                    if deftable.contains_key(name) {
                        let needed_expr = deftable.get(name).unwrap().clone();
                        *expr = needed_expr
                    }
                }
                _ => {}
            }
        }
        with_inline_def_impl(&mut new_expr, deftable);
        Stmt::Def(name.to_string(), new_expr)
    }
}

pub fn expand_all_lets(defs: Vec<Stmt>, deftable: &mut HashMap<String, Expr>) -> Vec<Stmt> {
    let mut new_defs = Vec::new();

    fn expand_all_lets_impl(expr: &mut Expr, deftable: &mut HashMap<String, Expr>) {
        match expr {
            Expr::Let(name, box e1, box e2) => {
                expand_all_lets_impl(e1, deftable);
                deftable.insert(name.clone(), e1.clone());
                expand_all_lets_impl(e2, deftable);
            }
            Expr::Apply(f, body) => {
                expand_all_lets_impl(f, deftable);
                expand_all_lets_impl(body, deftable);
            }
            Expr::Lambda(_, box body) => {
                expand_all_lets_impl(body, deftable);
            }
            Expr::Identifier(name) => {
                if deftable.contains_key(name) {
                    let needed_expr = deftable.get(name).unwrap().clone();
                    *expr = needed_expr
                }
            }
            _ => {}
        }
    }

    for def in defs {
        let Stmt::Def(name, expr) = def;
        let mut new_expr = expr.clone();
        deftable.insert(name.clone(), expr);

        expand_all_lets_impl(&mut new_expr, deftable);

        new_defs.push(Stmt::Def(name, new_expr));
    }

    new_defs
}
