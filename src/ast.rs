use std::fmt::{Debug};

#[derive(Debug)]
pub enum Expr {
    Number(i32),
    Op(Box<Expr>, Opcode, Box<Expr>),
    FunctionCall(Box<Expr>, Vec<Box<Expr>>),
    Conditional(Box<Expr>, Box<Expr>, Box<Expr>),
    Identifier(String),
}

#[derive(Debug)]
pub enum Opcode {
    Mul,
    Div,
    Add,
    Sub,
}
