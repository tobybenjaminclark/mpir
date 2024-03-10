import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *

def type_ast_expression(ast, context) -> _type:
    x = Real('σ')
    match ast["TYPE"]:
        case "EXPRESSION_IDENTIFIER":
            return get_type_from_context(context, ast["IDENTIFIER"])
        case "EXPRESSION_NUMERICAL_LITERAL":
            y = ast["VALUE"]
            return type_create_singular(lambda: x == y)
        case "EXPRESSION_OPERATOR":
            if ast["IDENTIFIER"] == "+":
                l = type_ast_expression(ast["LEFT"], context)
                r = type_ast_expression(ast["RIGHT"], context)
                return T_Add(l, r)
            elif ast["IDENTIFIER"] == "*":
                l = type_ast_expression(ast["LEFT"], context)
                r = type_ast_expression(ast["RIGHT"], context)
                return T_Mult(l, r)
        case _:
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
            "IDENTIFIER": "*",
            "LEFT": {
                "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
                "VALUE": 2.000000
            },
            "RIGHT" : {
              "TYPE" : "EXPRESSION_NUMERICAL_LITERAL",
              "VALUE" : 2.000000
            }
        }
    }




c = context_create()
x = Real('σ')
t = type_create_singular(lambda: z3.And(x > 10, x < 20))
c = c + ('a', t)
t2 = type_ast_expression(expression_dict, c)
print(t2.logic.constraint())
