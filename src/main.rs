use std::fmt;

use algo_j::syntax::Expr;
use chumsky::{prelude::*, text::keyword};
fn main() {
    let src = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    println!("{:?}", parser().parse(src));
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    let identifier = text::ident::<char, Simple<char>>();

    let expr = recursive(|expr| {
        let number = text::int::<char, Simple<char>>(10).padded();
        let e_ident = identifier.map(Expr::Identifier);

        let int = just('-').or_not().then(number).map(|(is_neg, num_str)| {
            let number: i32 = num_str.parse().unwrap();
            if is_neg.is_some() {
                Expr::Int(-number)
            } else {
                Expr::Int(number)
            }
        });

        let lambda = just("fun")
            .ignore_then(identifier.padded())
            .then_ignore(just("->"))
            .then(expr.clone().padded())
            .map(|(name, body)| Expr::Lambda(name, Box::new(body)));

        let let_ = just("let")
            .ignore_then(identifier.padded())
            .then_ignore(just('='))
            .then(expr.clone().padded())
            .then_ignore(just("in"))
            .then(expr.clone().padded())
            .map(|((name, e0), e1)| Expr::Let(name, Box::new(e0), Box::new(e1)));

        // let apply = expr
        //     .clone()
        //     .then(expr.clone().separated_by(just(' ')))
        //     .map(|(f, args)| {
        //         args.into_iter()
        //             .fold(f, |f, arg| Expr::Apply(Box::new(f), Box::new(arg)))
        //     });

        choice((let_, lambda, int, e_ident))
    });

    expr
}
