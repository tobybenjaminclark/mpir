import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *
import json


# Converts an operator node to Z3 logic.
def convert_operator_to_z3(operator: str, left, right):
    operator_mapping = {
        # Comparators
        ">": lambda: left > right, ">=": lambda: left >= right, "<": lambda: left < right, "<=": lambda: left <= right, "=": lambda: left == right,
        
        # Negation, Conjunction & Disjunction
        "∧": lambda:z3.And(left, right), "∨": lambda: z3.Or(left, right), "¬": lambda: z3.Not(left),

        # Predicates (Forall, Exists)
        "∀": lambda: z3.ForAll(left, right), "∃": lambda: z3.Exists(left, right),
    }
    return operator_mapping.get(operator, lambda: None)()


# Converts an expression to Z3 logic.
def form_expression(type_logic: dict):
    match type_logic["DATATYPE"]:
        case "OPERATOR":            return convert_operator_to_z3(type_logic["DATA"], form_expression(type_logic["LEFT"]), form_expression(type_logic["RIGHT"]))
        case "IDENTIFIER":          return z3.Real('σ')
        case "NUMERICAL_LITERAL":   return z3.RealVal(type_logic["DATA"]) 
        case _:                     return None


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
        




c = context_create()

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


# Function to process type declarations and add them to the typing context (Γ)
def process_type_declarations(ast: dict[str:any], Γ: _context) -> dict[str:_type]:
    types = {node["IDENTIFIER"]: node["LOGIC"] for node in filter(lambda node: node["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])}
    for k, v in types.items(): Γ += (k, type_create_singular(lambda: form_expression(v)))
    return Γ


def typecheck_type_assignment(statement: dict[str:any], context: _context) -> _context:
    typ = get_type_from_context(context, statement["ASSIGNED_TYPE"])
    if(typ == None):
        raise Exception("Type",statement["ASSIGNED_TYPE"],"not in context:",context)
    print("Let", statement["IDENTIFIER"], " :: ", typ.logic.constraint())
    identifier = statement["IDENTIFIER"]
    context = context + (identifier, typ)
    return context

def typecheck_value_assignment(statement: dict[str:any], context: _context) -> _context:
    expr = type_ast_expression(statement["EXPRESSION"], context)
    print("Set", statement["IDENTIFIER"], " :: ", expr.logic.constraint())
    if(expr < get_type_from_context(context, statement["IDENTIFIER"])):
        print("\t Valid")
    else:
        print("\t Not valid")
    return context

# Function to type check a Function Declaration
def typecheck_function(function: dict[str:any], context: _context):
    for statement in function["BODY"]:
        if statement["TYPE"] == "TYPE_ASSIGNMENT": context = typecheck_type_assignment(statement, context)
        if statement["TYPE"] == "VALUE_ASSIGNMENT": context = typecheck_value_assignment(statement, context)


# Function to type check an AST
def typecheck_ast(ast: dict[str:any]):
    Γ = context_create('Γ')
    Γ = process_type_declarations(ast, Γ)
    function_declarations = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]

    for function in function_declarations:
        typecheck_function(function, duplicate_context(Γ))


typecheck_ast(ast)
