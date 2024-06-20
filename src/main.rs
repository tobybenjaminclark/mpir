

use lalrpop_util::lalrpop_mod;

// Import the ast module
mod ast;

lalrpop_mod!(pub calculator1);

fn main() {
    calculator4();
    return;
}

fn calculator4() {
    let expr = calculator1::BlockParser::new()
        .parse(
            "{
            a := 5;
            5 + 10
            }"
        )
        .unwrap();
    println!("{:?}", expr);
}
