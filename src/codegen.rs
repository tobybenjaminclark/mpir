use crate::ast::{Block, Expr, Opcode, Program, Statement, TypedArgument};

pub fn generate_program(program: Program) -> String {
    match program {
        Program::Program(blocks) => {
            let mut result = String::new();
            for block in blocks {
                result.push_str(&generate_block(*block));
                result.push_str("\n\n");
            }
            result
        }
    }
}

pub fn generate_block(block: Block) -> String {
    match block {
        Block::FunctionDefinition(name, args, body_expr, statements) => {
            let name_str = generate_expr(*name);
            let args_str = args
                .into_iter()
                .map(|arg| generate_typed_argument(*arg))
                .collect::<Vec<String>>()
                .join(", ");
            let body_expr_str = generate_expr(*body_expr);
            let statements_str = statements
                .into_iter()
                .map(|stmt| generate_statement(*stmt))
                .collect::<Vec<String>>()
                .join("\n    ");

            format!("def {}({}) -> {}:\n    {}\n", name_str, args_str, body_expr_str, statements_str)
        }
    }
}



pub fn generate_typed_argument(arg: TypedArgument) -> String {
    match arg {
        TypedArgument::TypedArgument(name, type_expr) => {
            let name_str = generate_expr(*name);
            let type_expr_str = generate_expr(*type_expr);
            format!("{}: {}", name_str, type_expr_str)
        }
    }
}



pub fn generate_statement(statement: Statement) -> String {
    match statement {
        Statement::Assignment(left_expr, right_expr) => {
            let left_str = generate_expr(*left_expr);
            let right_str = generate_expr(*right_expr);
            format!("{} = {}", left_str, right_str)
        }
        Statement::TypeAssignment(left_expr, right_expr) => {
            let left_str = generate_expr(*left_expr);
            let right_str = generate_expr(*right_expr);
            format!("{}: {}", left_str, right_str) // Assuming mutable type assignment
        }
        Statement::Expr(expr) => generate_expr(expr),
    }
}



pub fn generate_expr(expr: Expr) -> String {
    match expr {
        Expr::Number(num) => num.to_string(),
        Expr::Op(left_expr, opcode, right_expr) => {
            let left_str = generate_expr(*left_expr);
            let right_str = generate_expr(*right_expr);
            let op_str = match opcode {
                Opcode::Mul => "*",
                Opcode::Div => "/",
                Opcode::Add => "+",
                Opcode::Sub => "-",
            };
            format!("{} {} {}", left_str, op_str, right_str)
        }
        Expr::FunctionCall(func_expr, args) => {
            let func_str = generate_expr(*func_expr);
            let args_str = args
                .into_iter()
                .map(|arg| generate_expr(*arg))
                .collect::<Vec<String>>()
                .join(", ");
            format!("{}({})", func_str, args_str)
        }
        Expr::Conditional(cond_expr, true_expr, false_expr) => {
            let cond_str = generate_expr(*cond_expr);
            let true_str = generate_expr(*true_expr);
            let false_str = generate_expr(*false_expr);
            format!("if {} {{ {} }} else {{ {} }}", cond_str, true_str, false_str)
        }
        Expr::Identifier(name) => name,
    }
}

