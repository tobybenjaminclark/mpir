
use lalrpop_util::lalrpop_mod;
use crate::ast::*;
use crate::codegen::*;

// Import the ast module
mod ast;
mod codegen;

lalrpop_mod!(pub calculator1);



fn main() {
    calculator4();
    return;
}

fn calculator4() {
    let expr: Box<Program> = calculator1::ProgramParser::new()
        .parse(
            "
            function (a:b, c:d) -> d {
                a: int;
                a := f(a);
                5 + 10;
            };

            function (a:b, c:d) -> d {
                a: int;
                a := f(a) + 200 + -500 * 2 + f(c + f(a),d,e);
                5 + 10;
            }
            "
        )
        .unwrap();
    println!("{:#?}", expr);
    let a = generate_program(*expr);
    println!("{a}");
}
