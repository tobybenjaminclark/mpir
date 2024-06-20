

use lalrpop_util::lalrpop_mod;

// Import the ast module
mod ast;

lalrpop_mod!(pub calculator1);

fn main() {
    calculator4();
    return;
}

fn calculator4() {
    let expr = calculator1::ExprParser::new()
        .parse("22 * 44 + 66 + f(1     , 2 + 5    ) + (if (a) then (b) else if ab then cd else e2)")
        .unwrap();
    println!("{:?}", expr);
}
