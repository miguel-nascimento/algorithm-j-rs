#[derive(Debug, Clone)]
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
