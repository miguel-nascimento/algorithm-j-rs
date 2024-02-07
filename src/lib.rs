#![feature(box_patterns)]

/// Implementation of the Hindley-Milner type system
/// https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
/// using the Algorithm J
use anyhow::Result;
use std::{
    collections::HashMap,
    sync::atomic::{AtomicUsize, Ordering},
};

#[derive(PartialEq, Hash, Eq, Clone)]
enum Type {
    /// _|_
    Unit,
    /// a
    Var(Scope),
    /// a -> b
    Arrow(Box<Type>, Box<Type>),
}

/// Efficient generalization with levels
/// https://okmij.org/ftp/ML/generalization.html#levels
static LEVEL: AtomicUsize = AtomicUsize::new(0);
static TYPEVAR_LEVEL: AtomicUsize = AtomicUsize::new(0);

#[derive(PartialEq, Hash, Eq)]
struct BoundVar {
    bounded: Type,
    level: i32,
}

impl BoundVar {
    pub fn enter_level() {
        LEVEL.fetch_add(1, Ordering::Relaxed);
    }
    pub fn exit_level() {
        LEVEL.fetch_sub(1, Ordering::Relaxed);
    }
}

type VarId = usize;

#[derive(PartialEq, Hash, Eq)]
enum TypeVar {
    Bound(BoundVar),
    Free(String),
}

#[derive(PartialEq, Hash, Eq, Clone)]
enum Scope {
    Bound(Box<Type>),
    Unbound(VarId),
}

/// Types that contains variable bound by zero or more forall
struct PolyType {
    vars: Vec<VarId>,
    t: Box<Type>,
}

impl PolyType {
    /// Takes a type with type vars inside and returns a polytype, with the type vars generalized inside the forall
    fn generalize(t: Type) -> PolyType {
        todo!()
    }
    /// Marks a type as not generalizable
    fn dont_generalize(t: Type) -> PolyType {
        todo!()
    }

    // Specialize a polytype by replacing bound type variables by new monotype variables
    fn inst(&self) -> Type {
        let mut type_table: HashMap<VarId, Type> = HashMap::new();
        for var_id in self.vars.iter() {
            type_table.insert(*var_id, Type::new_var());
        }
        self.t.replace_vars(&type_table)
    }
}

enum Expr {
    /// Identifier
    /// `x`
    Identifier(String),
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

impl Type {
    fn new_var() -> Type {
        let id = TYPEVAR_LEVEL.fetch_add(1, Ordering::Relaxed);
        Type::Var(Scope::Unbound(id))
    }

    /// Replace vars that can be found in the table. Leave they if not found
    fn replace_vars(&self, table: &HashMap<VarId, Type>) -> Self {
        match self {
            Type::Unit => Type::Unit,
            Type::Var(Scope::Bound(box t)) => t.replace_vars(table),
            Type::Var(Scope::Unbound(id)) => match table.get(&id) {
                Some(t) => t.clone(),
                None =>  Type::Var(Scope::Unbound(*id))
            },
            Type::Arrow(box a, box b) => {
                Type::Arrow(Box::new(a.replace_vars(table)), Box::new(b.replace_vars(table)))
            }
        }
    }
}

struct Env {
    polytypes: HashMap<String, PolyType>,
}

impl Env {
    fn infer(&mut self, expr: Expr) -> anyhow::Result<Type> {
        match expr {
            // Var rule
            // x : polytype_a ∈ Γ  t = inst(polytype_a)
            // -----------------------
            // Γ ⊢ x : t
            Expr::Identifier(x) => {
                let a = self
                    .polytypes
                    .get(&x)
                    .ok_or_else(|| anyhow::anyhow!("Unbound variable"))?;
                let t = PolyType::inst(a);
                Ok(t)
            }
            // Lambda rule
            // t = newvar()  Γ, x :   
            Expr::Lambda(_, _) => todo!(),
            Expr::Apply(_, _) => todo!(),
            Expr::Let(_, _, _) => todo!(),
        }
    }
}
