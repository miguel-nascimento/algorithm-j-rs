use crate::syntax::Expr;
/// Implementation of the Hindley-Milner type system
/// https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system
/// using the Algorithm J
use anyhow::bail;
use std::{
    cell::RefCell,
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
static LEVEL: AtomicUsize = AtomicUsize::new(0);

#[derive(PartialEq, Eq)]
struct BoundVar {
    bounded: Type,
    level: i32,
}

fn enter_level() {
    LEVEL.fetch_add(1, Ordering::Relaxed);
}
fn exit_level() {
    LEVEL.fetch_sub(1, Ordering::Relaxed);
}

type VarId = usize;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum TypeVar {
    Bound { t: Type },
    Unbound { id: VarId, level: RefCell<usize> },
}

/// Types that contains variable bound by zero or more forall
#[derive(PartialEq, Eq, Clone, Debug)]
struct PolyType {
    vars: Vec<VarId>,
    t: Box<Type>,
}

impl Display for PolyType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.vars.is_empty() {
            write!(f, "{}", self.t)
        } else {
            write!(
                f,
                "∀[{}] {}",
                self.vars
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                self.t
            )
        }
    }
}

impl PolyType {
    /// Takes a type with type vars inside and returns a polytype, with the type vars generalized inside the forall
    fn generalize(t: Type) -> PolyType {
        let mut typ_ids = vec![];

        match &t {
            Type::Var(var) => match &*var.borrow() {
                TypeVar::Bound { t } => {
                    PolyType::generalize(t.clone());
                }
                TypeVar::Unbound { id, level } => {
                    if *level.borrow() >= LEVEL.load(Ordering::Relaxed) {
                        typ_ids.push(*id);
                    }
                }
            },
            Type::Arrow(box f, box body) => {
                PolyType::generalize(f.clone());
                PolyType::generalize(body.clone());
            }
            _ => {}
        }

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

static TYPEVAR_ID: AtomicUsize = AtomicUsize::new(0);

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "unit"),
            Type::Int => write!(f, "int"),
            Type::Var(tv) => match &*tv.borrow() {
                TypeVar::Bound { t } => write!(f, "{}", t),
                TypeVar::Unbound { id, .. } => write!(f, "'{}", (id + 97) as u8 as char),
            },
            Type::Arrow(box a, box b) => write!(f, "({} -> {})", a, b),
        }
    }
}
impl Type {
    pub fn new_var() -> Type {
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
            Type::Int => Type::Int,
            Type::Var(tv) => match &*tv.borrow() {
                TypeVar::Bound { t } => t.replace_vars(table),
                TypeVar::Unbound { id, .. } => match table.get(&id) {
                    Some(t) => t.clone(),
                    None => Type::Var(tv.clone()),
                },
            },
            Type::Arrow(box a, box b) => Type::Arrow(
                Box::new(a.replace_vars(table)),
                Box::new(b.replace_vars(table)),
            ),
        }
    }

    /// Unify algorithm in J performs mutation, so it doesnt return another type
    pub fn unify(&self, other: &Type) -> anyhow::Result<()> {
        match (self, other) {
            (Type::Unit, Type::Unit) => Ok(()),
            (Type::Var(var), b) => {
                let mut type_var = var.borrow_mut();
                match &*type_var {
                    TypeVar::Bound { t: a } => a.unify(b),
                    TypeVar::Unbound { id, level } => {
                        if *self == *other {
                            return Ok(());
                        }

                        if occurs_check(*id, *level.borrow(), b) {
                            bail!("Type Error (occurs check)");
                        }
                        let b_bound = TypeVar::Bound { t: b.clone() };
                        *type_var = b_bound;
                        Ok(())
                    }
                }
            }
            (a, Type::Var(var)) => {
                let mut type_var = var.borrow_mut();
                match &*type_var {
                    TypeVar::Bound { t: b } => b.unify(a),
                    TypeVar::Unbound { id, level } => {
                        if *self == *other {
                            return Ok(());
                        }

                        if occurs_check(*id, *level.borrow(), a) {
                            bail!("Type Error (occurs check)");
                        }
                        let a_bound = TypeVar::Bound { t: a.clone() };
                        *type_var = a_bound;
                        Ok(())
                    }
                }
            }
            (Type::Arrow(param1, body1), Type::Arrow(param2, body2)) => {
                param1.unify(param2)?;
                body1.unify(body2)?;
                Ok(())
            }
            (a, b) => bail!("Type Error {a:?} with {b:?}"),
        }
    }
}

/// Check if a mono Var(a) can be found in a type
fn occurs_check(a_id: VarId, a_level: usize, type_: &Type) -> bool {
    match type_ {
        Type::Unit => false,
        Type::Int => false,
        Type::Var(tv) => match &*tv.borrow() {
            TypeVar::Bound { t } => occurs_check(a_id, a_level, &t),
            TypeVar::Unbound { id, level } => {
                let min = std::cmp::min(a_level, *level.borrow());
                level.replace(min);
                a_id == *id
            }
        },
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
    pub fn infer(&mut self, expr: Expr) -> anyhow::Result<Type> {
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
            // typeof int => int
            Expr::Int(_) => Ok(Type::Int),
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
            // t0 = Γ ⊢ f
            // t1 = Γ ⊢ x
            // t' = newvar() // aka dummy var
            // unify(t0, t1 -> t')
            // --------------------
            // Γ ⊢ e0 e1 : t'
            Expr::Apply(box f, box x) => {
                let t0 = self.infer(f)?;
                let t1 = self.infer(x)?;
                let t_prime = Type::new_var();
                t0.unify(&Type::Arrow(
                    Box::new(t1.clone()),
                    Box::new(t_prime.clone()),
                ))?;
                Ok(t0)
            }
            // Let rule
            // t = infer env e0
            // t' = infer new_env_with_x_e0 e1
            // --------------------
            // Γ ⊢ let x = e0 in e1 : t'
            Expr::Let(x, box e0, box e1) => {
                enter_level();
                let t = self.infer(e0)?;
                exit_level();

                let mut new_env = self.clone();
                let generalized_t = PolyType::generalize(t);
                new_env.insert(x, generalized_t);
                let t_prime = new_env.infer(e1)?;
                Ok(t_prime)
            }
        }
    }
}

// with debrujin index and levels, we can generalize HM to System-F
// allowing for higher rank polymorphism

#[test]
fn test_expr() {
    // let id = \x -> x
    // id 1
    let let_test = Expr::Let(
        "id".to_string(),
        Box::new(Expr::Lambda(
            "x".to_string(),
            Box::new(Expr::Identifier("x".to_string())),
        )),
        Box::new(Expr::Apply(
            Box::new(Expr::Identifier("id".to_string())),
            Box::new(Expr::Int(1)),
        )),
    );

    let mut env = Env { polytypes: vec![] };
    let result = env.infer(let_test).unwrap();
    assert_eq!(result, Type::Int)
}
