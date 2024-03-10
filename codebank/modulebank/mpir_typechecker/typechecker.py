import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *

def type_ast_expression(ast, context, σ = z3.Real('σ')) -> _type:
    ast_type = ast["TYPE"]
    if ast_type == "EXPRESSION_IDENTIFIER":
        return get_type_from_context(context, ast["IDENTIFIER"])
    if ast_type ==  "EXPRESSION_NUMERICAL_LITERAL":
        y = ast["VALUE"]
        return type_create_singular(lambda: σ == y)
    if ast_type == "EXPRESSION_OPERATOR":
        left = type_ast_expression(ast["LEFT"], context)
        right = type_ast_expression(ast["RIGHT"], context)
        if ast["IDENTIFIER"] == "+":
            return T_Add(left, right)
        elif ast["IDENTIFIER"] == "*":
            return T_Mult(left, right)
        elif ast["IDENTIFIER"] == "-":
            return T_Sub(left, right)
        elif ast["IDENTIFIER"] == "/":
            return T_Div(left, right)
    else:
        print("Error!")



expression_dict = {
        "TYPE": "EXPRESSION_OPERATOR",
        "IDENTIFIER": "+",
        "LEFT": {
            "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
            "VALUE": 5.000000
        },
        "RIGHT": {
            "TYPE": "EXPRESSION_OPERATOR",
            "IDENTIFIER": "+",
            "LEFT": {
                "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
                "VALUE": 4.000000
            },
            "RIGHT" : {
              "TYPE" : "EXPRESSION_IDENTIFIER",
              "IDENTIFIER" : "a"
            }
        }
    }




c = context_create()
x = Real('σ')
t = type_create_singular(lambda: z3.And(x > 10, x < 20))
c = c + ('a', t)
t2 = type_ast_expression(expression_dict, c)
print(t2.logic.constraint())
