import z3
from typing_context import *
from typing_context import _type, _context
from core_calculus import *
from typing import Literal, IO
import json

DEBUG_MODE = True

def debug(*args, sep: str | None = " ", end: str | None = "\n", flush: Literal[False] = False) -> None:
    return print(">>",*args, sep = sep, end = end, flush = flush) if DEBUG_MODE else None

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


# Function to process type declarations and add them to the typing context (Γ).
def process_type_declarations(ast: dict[str:any], Γ: _context) -> dict[str:_type]:
    types = {node["IDENTIFIER"]: node["LOGIC"] for node in filter(lambda node: node["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])}
    for k, v in types.items(): Γ += (k, type_create_singular(lambda: form_expression(v)))
    return Γ



# Function to typecheck a type assignment/let statement.
def typecheck_type_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    assigned_type = get_type_from_context(Γ, statement["ASSIGNED_TYPE"])

    if(assigned_type == None): raise Exception("Type",statement["ASSIGNED_TYPE"],"not in context:",Γ)
    debug("Let", statement["IDENTIFIER"], " :: ", assigned_type.logic.constraint())

    return add_type_to_context(Γ, statement["IDENTIFIER"], assigned_type), add_type_to_context(Ψ, statement["IDENTIFIER"], assigned_type)



# Function to typecheck a value assignment/set statement.
def typecheck_value_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    expr = type_ast_expression(statement["EXPRESSION"], Ψ)

    debug("Set", statement["IDENTIFIER"], " :: ", expr.logic.constraint())

    # Set Statement is valid
    if(expr < get_type_from_context(Γ, statement["IDENTIFIER"])):
        debug("\t Valid")  
        Ψ += (statement["IDENTIFIER"], expr)
    
    # Set Statement is not valid
    else:
        raise Exception("Invalid Set Statement :: Expression is not a subtype of asignee.")

    return Γ, Ψ



# Function to typecheck a function call.
def typecheck_function_call(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    print("Function Call to", statement["IDENTIFIER"])

    # Validating function call is correct.
    if statement["IDENTIFIER"] not in Γ: raise Exception("Use of an undeclared function!")
    if get_type_from_context(Γ, statement["IDENTIFIER"]).type != type_variants._function: raise Exception("Using a non-function type as a function type.")
    function = get_type_from_context(Γ, statement["IDENTIFIER"])

    # Validate Inputs
    for index, passed_argument in enumerate(statement["ARGUMENTS"]):
        argument_type =  type_create_singular(function.logic.input_constraints[index])
        passed_type = type_ast_expression(passed_argument["VALUE"], Ψ)
        if not (passed_type < argument_type):
            raise Exception("Argument type not subtype of required type")
        else:
            print("Valid Argument")
    
    return Γ, Ψ 



# Function to type check a Function Declaration.
def typecheck_function(function: dict[str:any], Γ: _context):
    print(function)

    # Binding Base Types and `return` function type.
    Γ = Γ + ("Integer", type_create_singular(True)) 
    Γ = Γ + ("return", type_create_function([get_type_from_context(Γ, type_identifier).logic.constraint for type_identifier in function["INPUTS"]], get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint))

    Ψ = context_create('Ψ')
    for statement in function["BODY"]:
        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT": Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)



# Function to type check an AST
def typecheck_ast(ast: dict[str:any]):
    Γ = context_create('Γ')
    Γ = process_type_declarations(ast, Γ)
    function_declarations = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]

    for function in function_declarations:
        typecheck_function(function, duplicate_context(Γ))


typecheck_ast(ast)
