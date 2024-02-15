use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar); // synthesized by LALRPOP

fn main() {
    let ast = grammar::StmtParser::new()
        .parse(r#"let id = (fun x -> x) in let id = id () in a;"#)
        .unwrap();
    println!("{:?}", ast);
}
