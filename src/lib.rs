#![feature(box_patterns)]

/// Implementation of the Hindley-Milner type system
/// https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
/// using the Algorithm J
use anyhow::Result;
use std::{
    collections::HashMap,
    sync::atomic::{AtomicUsize, Ordering},
};

#[derive(PartialEq, Hash, Eq)]
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

#[derive(PartialEq, Hash, Eq)]
enum Scope {
    Bound(Box<Type>),
    Unbound(VarId),
}

/// PolyType = `Forall [a b c]. a -> b -> c`
struct PolyType {
    vars: Vec<TypeVar>,
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

    fn replace_vars(&self, table: &TypeTable) -> PolyType {
        match self {
            Type::Unit => PolyType::dont_generalize(Type::Unit),
            Type::Var(var) => match var {
                Scope::Bound(box t) => t.replace_vars(table),
                Scope::Unbound(id) => match table.lookup(id) {
                    Some(t) => t.replace_vars(table),
                    None => PolyType::dont_generalize(Type::new_var()),
                },
            },
            Type::Arrow(a, b) => {
                todo!()
            }
        };

        todo!()
    }
}

struct Env {
    bindings: HashMap<String, PolyType>,
}

struct TypeTable {
    bindings: HashMap<VarId, Type>,
}

impl TypeTable {
    fn lookup(&self, x: &VarId) -> Option<&Type> {
        self.bindings.get(x)
    }
    // Instantiates a polytype by replacing the type vars with fresh type vars
    fn inst(&mut self, type_: &PolyType) {
        todo!()
    }
}

impl Env {
    fn lookup(&self, x: &str) -> Option<&PolyType> {
        self.bindings.get(x)
    }
    fn infer(&mut self, expr: Expr, type_table: &mut TypeTable) -> anyhow::Result<Type> {
        match expr {
            // Var rule
            // x : a ∈ Γ  t = inst(a)
            // -----------------------
            // Γ ⊢ x : t
            Expr::Identifier(x) => {
                let a = self
                    .lookup(&x)
                    .ok_or_else(|| anyhow::anyhow!("Unbound variable"))?;
                let t = type_table.inst(a);
            }
            Expr::Lambda(_, _) => todo!(),
            Expr::Apply(_, _) => todo!(),
            Expr::Let(_, _, _) => todo!(),
        }
        todo!()
    }
}
