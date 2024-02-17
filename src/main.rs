use std::{collections::HashMap, sync::atomic::Ordering};

use algo_j::{
    hm::{Env, TYPEVAR_ID},
    syntax::expand_all_lets,
};
use colored::Colorize;
use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar);

fn main() {
    let mut args = std::env::args();
    match &args.len() {
        1 => repl(),
        _ => {
            let filename = args.nth(1).unwrap();
            typecheck_file(filename)
        }
    }
}

fn repl() {
    let mut deftable = HashMap::new();
    let mut env = Env::default();
    loop {
        let mut input = String::new();
        let stdin = std::io::stdin();
        stdin.read_line(&mut input).unwrap();

        let parsed = grammar::StmtParser::new().parse(&input);
        if let Err(parse_error) = &parsed {
            eprintln!("Parse error: {parse_error}");
            continue;
        }
        let expanded_stmt = parsed.unwrap().with_inline_def(&mut deftable);

        let type_ = expanded_stmt.type_of(&mut env);
        if let Err(type_error) = type_ {
            eprintln!("Type error: {type_error}");
            continue;
        }
        println!(
            "    {} ⊢ {}",
            &expanded_stmt.get_name().bright_magenta(),
            type_.unwrap().to_string().bright_black(),
        );
        deftable.insert(expanded_stmt.get_name(), expanded_stmt.get_expr());
        TYPEVAR_ID.store(0, Ordering::Relaxed);
    }
}

fn typecheck_file(filename: String) {
    let file = std::fs::read_to_string(filename).expect("Failed to read file");
    let ast = grammar::StmtsParser::new().parse(&file).unwrap();

    let mut env = Env::default();
    let mut deftable = HashMap::new();
    let new_ast = expand_all_lets(ast, &mut deftable);

    for stmt in new_ast.into_iter() {
        TYPEVAR_ID.store(0, Ordering::Relaxed);
        let expanded_stmt = stmt.with_inline_def(&mut deftable);
        let type_ = expanded_stmt.type_of(&mut env).unwrap();
        println!(
            "{} ⊢ {}",
            expanded_stmt.get_name().bright_magenta(),
            type_.to_string().bright_black(),
        );
    }
}
