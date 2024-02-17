use crate::syntax::Expr;
/// Implementation of the Hindley-Milner type system
/// https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
/// using the Algorithm J
use anyhow::{anyhow, bail};
use std::{
    cell::RefCell,
    cmp::min,
    collections::HashMap,
    fmt::Display,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    /// _|_
    Unit,
    /// a
    Var(Rc<RefCell<TypeVar>>),
    /// a -> b
    Arrow(Box<Type>, Box<Type>),
    /// Expr Int
    Int,
}

/// Efficient generalization with levels
/// https://okmij.org/ftp/ML/generalization.html#levels
pub static LEVEL: AtomicUsize = AtomicUsize::new(0);

fn enter_level() {
    LEVEL.fetch_add(1, Ordering::Relaxed);
}
fn exit_level() {
    LEVEL.fetch_sub(1, Ordering::Relaxed);
}

type VarId = usize;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TypeVar {
    Bound {
        t: Type,
    },
    Unbound {
        id: VarId,
        level: Rc<RefCell<usize>>,
    },
}

/// Types that contains variable bound by zero or more forall
#[derive(PartialEq, Eq, Clone, Debug)]
struct PolyType {
    vars: Vec<VarId>,
    t: Box<Type>,
}

impl PolyType {
    /// Takes a type with type vars inside and returns a polytype, with the type vars generalized inside the forall
    fn generalize(t: Type) -> PolyType {
        let mut typ_ids = vec![];

        fn generalize_impl(t: &Type, typ_ids: &mut Vec<VarId>) {
            match t {
                Type::Var(var) => match &mut *var.borrow_mut() {
                    TypeVar::Bound { t } => {
                        generalize_impl(t, typ_ids);
                    }
                    TypeVar::Unbound { id, level } => {
                        if *level.borrow() > LEVEL.load(Ordering::Relaxed) {
                            typ_ids.push(*id);
                        }
                    }
                },
                Type::Arrow(box f, box body) => {
                    generalize_impl(f, typ_ids);
                    generalize_impl(body, typ_ids);
                }
                _ => {}
            }
        }

        generalize_impl(&t, &mut typ_ids);
        typ_ids.sort();
        typ_ids.dedup();
        PolyType {
            vars: typ_ids,
            t: Box::new(t),
        }
    }
    /// Marks a type as not generalizable
    fn dont_generalize(t: Type) -> PolyType {
        PolyType {
            vars: vec![],
            t: Box::new(t),
        }
    }

    /// Specialize a polytype by replacing bound type variables by new monotype variables
    fn inst(&self) -> Type {
        let mut type_table: HashMap<VarId, Type> = HashMap::new();
        for var_id in self.vars.iter() {
            type_table.insert(*var_id, Type::new_var());
        }
        self.t.replace_vars(&type_table)
    }
}

pub static TYPEVAR_ID: AtomicUsize = AtomicUsize::new(0);

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // If there's an arrow inside, we should parenthesize it
        fn should_parenthesize(t: &Type) -> bool {
            match t {
                Type::Var(var) => {
                    let type_var = var.borrow_mut();
                    match &*type_var {
                        TypeVar::Bound { t } => should_parenthesize(t),
                        TypeVar::Unbound { .. } => false,
                    }
                }
                Type::Arrow(_, _) => true,
                _ => false,
            }
        }

        match self {
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Var(tv) => match &*tv.borrow() {
                TypeVar::Bound { t } => write!(f, "{}", t),
                TypeVar::Unbound { id, .. } => write!(f, "'{}", (id + 97) as u8 as char),
            },
            Type::Arrow(box a, box b) => {
                if should_parenthesize(a) {
                    write!(f, "({}) -> {}", a, b)
                } else {
                    write!(f, "{} -> {}", a, b)
                }
            }
        }
    }
}
impl Type {
    pub fn new_var() -> Type {
        let id = TYPEVAR_ID.fetch_add(1, Ordering::Relaxed);
        Type::Var(Rc::new(RefCell::new(TypeVar::Unbound {
            id,
            level: Rc::new(RefCell::new(LEVEL.load(Ordering::Relaxed))),
        })))
    }

    /// Unwrap the inner type of a Bound Var
    /// let bound_var = Expr::Var(Rc::new(RefCell::new { value: TypeVar::Bound { t: Type::Int } }));
    /// assert_eq!(bound_var.unwrap_boundvar(), Some(Type::Int))
    /// ```
    pub fn unwrap_boundvar(&self) -> Option<Type> {
        match self {
            Type::Var(tv) => match &*tv.borrow() {
                TypeVar::Bound { t } => Some(t.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Replace vars that can be found in the table. Leave they if not found
    fn replace_vars(&self, table: &HashMap<VarId, Type>) -> Self {
        match self {
            Type::Var(tv) => match &*tv.borrow() {
                TypeVar::Bound { t } => t.replace_vars(table),
                TypeVar::Unbound { id, .. } => match table.get(id) {
                    Some(t) => t.clone(),
                    None => Type::Var(tv.clone()),
                },
            },
            Type::Arrow(box a, box b) => Type::Arrow(
                Box::new(a.replace_vars(table)),
                Box::new(b.replace_vars(table)),
            ),
            _ => self.clone(),
        }
    }

    /// Check if a mono Var(a) can be found in a type
    pub fn occurs_check(&self, id: usize, level: usize) -> bool {
        match self {
            Type::Unit => false,
            Type::Int => false,
            Type::Var(tv) => {
                let tv = tv.try_borrow_mut();
                if tv.is_err() {
                    return true;
                }
                let mut tv = tv.unwrap();
                match &mut *tv {
                    TypeVar::Bound { t } => t.occurs_check(id, level),
                    TypeVar::Unbound {
                        id: var_id,
                        level: var_level,
                    } => {
                        let mut var_level = var_level.borrow_mut();
                        let min = min(level, *var_level);
                        *var_level = min;
                        *var_id == id
                    }
                }
            }
            Type::Arrow(box f, box body) => {
                f.occurs_check(id, level) || body.occurs_check(id, level)
            }
        }
    }

    /// Unify algorithm in J performs mutation, so it doesnt return another type
    pub fn unify(&self, other: &Type) -> anyhow::Result<()> {
        match (self, other) {
            (Type::Unit, Type::Unit) => Ok(()),
            (Type::Var(var), b) => {
                let var = var.try_borrow_mut();
                if var.is_err() {
                    return Err(anyhow!("occur check"));
                }
                let mut var = var.unwrap();
                match &mut *var {
                    TypeVar::Bound { t: a } => a.unify(b),
                    TypeVar::Unbound { id, level } => {
                        // FIXME: check if its right
                        // if &self == &other {
                        //     return Ok(());
                        // }
                        if b.occurs_check(*id, *level.borrow()) {
                            bail!("Type Error (occurs check)");
                        }
                        let b_bound = TypeVar::Bound { t: b.clone() };
                        *var = b_bound;
                        Ok(())
                    }
                }
            }
            (a, Type::Var(var)) => {
                let var = var.try_borrow_mut();
                if var.is_err() {
                    return Err(anyhow!("occur check"));
                }
                let mut var = var.unwrap();
                match &mut *var {
                    TypeVar::Bound { t: b } => b.unify(a),
                    TypeVar::Unbound { id, level } => {
                        // FIXME: check if its right
                        // if &self == &other {
                        //     return Ok(());
                        // }

                        if a.occurs_check(*id, *level.borrow()) {
                            bail!("Type Error (occurs check)");
                        }
                        let a_bound = TypeVar::Bound { t: a.clone() };
                        *var = a_bound;
                        Ok(())
                    }
                }
            }
            (Type::Arrow(box param1, box body1), Type::Arrow(box param2, box body2)) => {
                param1.unify(param2)?;
                body1.unify(body2)?;
                Ok(())
            }
            (a, b) => Err(anyhow!("Type Error {a:?} with {b:?}")),
        }
    }
}

#[derive(Clone, Default)]
pub struct Env {
    polytypes: Vec<(String, PolyType)>,
}

impl Env {
    fn get(&self, id: &str) -> Option<&PolyType> {
        self.polytypes
            .iter()
            .find(|(name, _)| name == id)
            .map(|(_, t)| t)
    }
    fn insert(&mut self, id: String, value: PolyType) {
        self.polytypes.push((id, value))
    }
    pub fn infer(&mut self, expr: Expr) -> anyhow::Result<Type> {
        match expr {
            // Unit rule
            // -----------------------
            // Γ ⊢ () : unit
            Expr::Unit => Ok(Type::Unit),
            // Int rule
            // -----------------------
            // Γ ⊢ n where n is Int : Int
            Expr::Int(_) => Ok(Type::Int),
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
            Expr::Lambda(x, box body) => {
                let dummy_var = Type::new_var(); // t
                let mut new_env = self.clone();
                new_env.insert(x, PolyType::dont_generalize(dummy_var.clone()));
                let expr_type = new_env.infer(body)?; // t'
                Ok(Type::Arrow(Box::new(dummy_var), Box::new(expr_type)))
            }
            // Application rule
            // t0 = Γ ⊢ f
            // t1 = Γ ⊢ x
            // t' = newvar() // aka dummy var
            // unify(t0, t1 -> t')
            // --------------------
            // Γ ⊢ e0 e1 : t'
            Expr::Apply(box f, box x) => {
                let t0 = self.infer(f)?; // a -> a
                let t1 = self.infer(x)?; // int
                let t_prime = Type::new_var(); // ?
                t0.unify(&Type::Arrow(Box::new(t1), Box::new(t_prime.clone())))?;
                Ok(t_prime)
            }
            // Let rule
            // t = infer env e0
            // t' = infer new_env_with_x_e1 e2
            // --------------------
            // Γ ⊢ let x = e1 in e2 : t'
            Expr::Let(x, box e1, box e2) => {
                enter_level();
                let t = self.infer(e1)?;
                exit_level();

                let mut new_env = self.clone();
                let generalized_t = PolyType::generalize(t);
                new_env.insert(x, generalized_t);
                let t_prime = new_env.infer(e2)?;
                Ok(t_prime)
            }
        }
    }
}
