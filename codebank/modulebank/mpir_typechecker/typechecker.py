import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *

# Function to infer the type of an expression operator node, from the types of it's constituents.
def type_ast_expression_operator(ast, context, σ=z3.Real('σ')) -> _type:
    op_mapping = {"+": T_Add, "*": T_Mult, "-": T_Sub, "/": T_Div}
    return op_mapping.get(ast["IDENTIFIER"], lambda: print("Error!"))(
        type_ast_expression(ast["LEFT"], context),
        type_ast_expression(ast["RIGHT"], context)
    )

# Function to infer the type of a numerical literal.
def type_ast_numerical_literal(ast, context, σ=z3.Real('σ')) -> _type:
    return type_create_singular(lambda: σ == ast["VALUE"])

# Function to infer the type of an ast expression.
def type_ast_expression(ast, context, σ = z3.Real('σ')) -> _type:
    ast_type = ast["TYPE"]
    if ast_type   == "EXPRESSION_IDENTIFIER":         return get_type_from_context(context, ast["IDENTIFIER"])
    elif ast_type ==  "EXPRESSION_NUMERICAL_LITERAL": return type_ast_numerical_literal(ast, context)
    elif ast_type == "EXPRESSION_OPERATOR":           return type_ast_expression_operator(ast, context)
    else:                                             print("Error!")
        



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
