import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *
import json


def convert_operator_to_z3(operator: str, left, right):
    operator_mapping = {
        # Comparators
        ">": lambda: left > right, ">=": lambda: left >= right, "<": lambda: left < right, "<=": lambda: left <= right, "=": lambda: left == right,
        # Negation, Conjunction & Disjunction
        "∧": lambda:z3.And(left, right), "∨": lambda: z3.Or(left, right), "¬": lambda: z3.Not(left),
        # Predicates (Forall, Exists)
        "∀": lambda: z3.ForAll(left, right), "∃": lambda: z3.Exists(left, right),
    }

    if operator in operator_mapping:
        return operator_mapping[operator]()
    else:
        # Handle the case where the operator is not recognized
        raise ValueError(f"Unsupported operator: {operator}")

def form_expression(type_logic: dict):

    match type_logic["DATATYPE"]:
        case "OPERATOR":
            left = form_expression(type_logic["LEFT"])
            right = form_expression(type_logic["RIGHT"])
            return convert_operator_to_z3(type_logic["DATA"], left, right)
        case "IDENTIFIER":
            return z3.Real('x')
        case "STRING_LITERAL":
            pass
        case "NUMERICAL_LITERAL":
            return z3.RealVal(type_logic["DATA"])  # Convert to Z3 Real value




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
    if ast_type   == "EXPRESSION_IDENTIFIER":         return t
    elif ast_type ==  "EXPRESSION_NUMERICAL_LITERAL": return type_ast_numerical_literal(ast, context)
    elif ast_type == "EXPRESSION_OPERATOR":           return type_ast_expression_operator(ast, context)
    else:                                             print("Error!")
        



expression_dict = {
    "TYPE" : "EXPRESSION_OPERATOR",
    "IDENTIFIER" : "+",
    "LEFT" : {
        "TYPE" : "EXPRESSION_NUMERICAL_LITERAL",
        "VALUE" : 5.000000
    },
    "RIGHT" : {
        "TYPE" : "EXPRESSION_OPERATOR",
        "IDENTIFIER" : "+",
        "LEFT" : {
            "TYPE" : "EXPRESSION_NUMERICAL_LITERAL",
            "VALUE" : 1.000000
        },
        "RIGHT" : {
            "TYPE" : "EXPRESSION_IDENTIFIER",
            "IDENTIFIER" : "z"
        }
    }}



c = context_create()
x = Real('σ')
t = type_create_singular(lambda: z3.And(0 < x, 100 > x))
c = c + ('z', t)
t2 = type_ast_expression(expression_dict, c)
print(t2.logic.constraint())

t3 = type_create_singular(lambda: True)
print(t3 < t2)

def parse_json_file(filename: str) -> dict|None:
    try:
        file = open(filename, 'r')
        data = json.load(file)
        file.close()
        return data
    except FileNotFoundError:
        print(f"File '{filename}' not found.")
        return None
    except json.JSONDecodeError as e:
        print(f"Error decoding AST in '{filename}': {e}")
        return None
    
ast = parse_json_file("testj.json")

types = {}
for node in ast["CONTENTS"]:
    if(node["TYPE"] == "TYPE_DECLARATION"):
        iden = node["IDENTIFIER"]
        types[iden] = node["LOGIC"]

for node in ast["CONTENTS"]:
        if "TYPE" in node and node["TYPE"] == "FUNCTION_DECLARATION":
            for statement in node["BODY"]:
                if statement["TYPE"] == "TYPE_ASSIGNMENT":
                    # TODO: Fix!
                    typ1 = types[statement["ASSIGNED_TYPE"]]
                    typ = form_expression(typ1)
                    print("LET", statement["IDENTIFIER"], " :: ", typ)
                    c += (statement["IDENTIFIER"], type_create_singular(lambda: typ))
                if statement["TYPE"] == "VALUE_ASSIGNMENT":
                    expr = type_ast_expression(statement["EXPRESSION"], c)
                    print("SET", statement["IDENTIFIER"], " :: ", expr.logic.constraint())
                

