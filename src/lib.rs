#![feature(box_patterns)]

/// Implementation of the Hindley-Milner type system
/// https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
/// using the Algorithm J
use anyhow::Result;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

#[derive(PartialEq, Eq, Clone)]
enum Type {
    /// _|_
    Unit,
    /// a
    Var(Rc<RefCell<TypeVar>>),
    /// a -> b
    Arrow(Box<Type>, Box<Type>),
}

/// Efficient generalization with levels
/// https://okmij.org/ftp/ML/generalization.html#levels
static LEVEL: AtomicUsize = AtomicUsize::new(0);

#[derive(PartialEq, Eq)]
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

#[derive(PartialEq, Eq, Clone)]
enum TypeVar {
    Bound { t: Type },
    Unbound { id: VarId, level: RefCell<usize> },
}

/// Types that contains variable bound by zero or more forall
#[derive(PartialEq, Eq, Clone)]
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

static TYPEVAR_ID: AtomicUsize = AtomicUsize::new(0);

impl Type {
    fn new_var() -> Type {
        let id = TYPEVAR_ID.fetch_add(1, Ordering::Relaxed);
        Type::Var(Rc::new(RefCell::new(TypeVar::Unbound {
            id,
            level: RefCell::new(LEVEL.load(Ordering::Relaxed)),
        })))
    }

    /// Replace vars that can be found in the table. Leave they if not found
    fn replace_vars(&self, table: &HashMap<VarId, Type>) -> Self {
        match self {
            Type::Unit => Type::Unit,
            Type::Var(tv) => {
                let a = tv.borrow();
                match &*a {
                    TypeVar::Bound { t } => t.replace_vars(table),
                    TypeVar::Unbound { id, .. } => match table.get(&id) {
                        Some(t) => t.clone(),
                        None => Type::Var(tv.clone()),
                    },
                }
            }
            Type::Arrow(box a, box b) => Type::Arrow(
                Box::new(a.replace_vars(table)),
                Box::new(b.replace_vars(table)),
            ),
        }
    }

    fn unify(&self, other: &Type) -> anyhow::Result<Type> {
        todo!()
    }
}

/// Check if a mono Var(a) can be found in a type
fn occurs_check(a_id: VarId, a_level: usize, type_: &Type) -> bool {
    match type_ {
        Type::Unit => false,
        Type::Var(tv) => {
            let a = tv.borrow();
            match &*a {
                TypeVar::Bound { t } => occurs_check(a_id, a_level, t),
                TypeVar::Unbound { id, level } => {
                    let min = std::cmp::min(a_level, *level.borrow());
                    level.replace(min);
                    a_id == *id
                }
            }
        }
        Type::Arrow(box f, box body) => {
            occurs_check(a_id, a_level, f) || occurs_check(a_id, a_level, body)
        }
    }
}

#[derive(Clone)]
struct Env {
    polytypes: Vec<(String, PolyType)>,
}

impl Env {
    fn get(&self, id: &str) -> Option<&PolyType> {
        self.polytypes
            .iter()
            .find(|(name, _)| name == id)
            .map(|(_, t)| t)
    }
    fn insert(&mut self, id: String, value: PolyType) -> () {
        self.polytypes.push((id, value))
    }
    fn infer(&mut self, expr: Expr) -> anyhow::Result<Type> {
        match expr {
            // Var rule
            // x : polytype_a ∈ Γ  t = inst(polytype_a)
            // -----------------------
            // Γ ⊢ x : t
            Expr::Identifier(x) => {
                let a = self
                    .get(&x)
                    .ok_or_else(|| anyhow::anyhow!("Unbound variable"))?;
                let t = PolyType::inst(a);
                Ok(t)
            }
            // Lambda rule
            // t = newvar() (aka dummy var)
            // t' = Γ, x : infer e
            // ___________________
            // Γ ⊢ \x -> e : t -> t'
            Expr::Lambda(x, body) => {
                let dummy_var = Type::new_var(); // t
                let mut new_env = self.clone();
                new_env.insert(x, PolyType::dont_generalize(dummy_var.clone()));
                let expr_type = new_env.infer(*body)?; // t'
                Ok(Type::Arrow(Box::new(dummy_var), Box::new(expr_type)))
            }
            // Application rule
            // t0 = Γ ⊢ e0
            // t1 = Γ ⊢ e1
            // t' = newvar() // aka dummy var
            // unify(t0, t1 -> t')
            // --------------------
            // Γ ⊢ e0 e1 : t'
            Expr::Apply(_, _) => todo!(),
            Expr::Let(_, _, _) => todo!(),
        }
    }
}
// TODO: occur check

// not var, is a "hole"

// Bidirectional Typing
// Constraint Based Typing
// https://matryoshka-project.github.io/pubs/hounif_paper.pdf

// with debrujin index and levels, we can generalize HM to System-F
// allowing for higher rank polymorphism
