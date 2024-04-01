import z3
import argparse
from typing_context import *
from typing_context import _type, _context
from core_calculus import *
from mpir_module_python import build_python
from typing import Literal, IO
import json

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



DEBUG_MODE = True

def debug(*args, sep: str | None = " ", end: str | None = "\n", flush: Literal[False] = False) -> None:
    return print(">>",*args, sep = sep, end = end, flush = flush) if DEBUG_MODE else None


# Converts an operator node to Z3 logic.
def convert_operator_to_z3(operator: str, left, right):
    operator_mapping = {
        # Comparators
        ">": lambda: left > right, "≥": lambda: left >= right, "<": lambda: left < right, "≤": lambda: left <= right, "=": lambda: left == right, "==": lambda: left == right,
        
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
def type_ast_expression_operator(ast, context, propagation, σ=z3.Real('σ')) -> _type:
    op_mapping = {"+": T_Add, "*": T_Mult, "-": T_Sub, "/": T_Div,
                  ">": T_Comp, ">=": T_Comp, "<": T_Comp, "<=": T_Comp, "^": T_Comp, "v": T_Comp}
    if ast["LEFT"]["TYPE"] == "EXPRESSION_IDENTIFIER" and ast["LEFT"]["IDENTIFIER"] not in propagation: raise Exception(f"Undeclared Identifier " + ast["LEFT"]["IDENTIFIER"])
    if ast["RIGHT"]["TYPE"] == "EXPRESSION_IDENTIFIER" and ast["RIGHT"]["IDENTIFIER"] not in propagation: raise Exception(f"Undeclared Identifier " + ast["RIGHT"]["IDENTIFIER"])
    return op_mapping.get(ast["IDENTIFIER"], lambda: print("Error!"))(
        type_ast_expression(ast["LEFT"], context, propagation),
        type_ast_expression(ast["RIGHT"], context, propagation)
    )



# Function to infer the type of a numerical literal.
def type_ast_numerical_literal(ast, context, σ=z3.Real('σ')) -> _type:
    return type_create_singular(lambda: σ == ast["VALUE"])



# Function to Type Check a Function Call as part of an expression.
def type_ast_function_call(ast, context, propagation, σ=z3.Real('σ')) -> _type:
    try:
        typ = T_FuncCall([type_ast_expression(arg["VALUE"], context, propagation) for arg in ast["ARGUMENTS"]], get_type_from_context(context, ast["IDENTIFIER"]))
        return typ
    except:
        print("Function Call Type Failure")
        print(type_ast_expression(arg["VALUE"], context, propagation) for arg in ast["ARGUMENTS"])
    

# Function to infer the type of an ast expression.
def type_ast_expression(ast, context, propagation, σ = z3.Real('σ')) -> _type:
    ast_type = ast["TYPE"]
    if ast_type   == "EXPRESSION_IDENTIFIER":         return get_type_from_context(propagation, ast["IDENTIFIER"])
    elif ast_type ==  "EXPRESSION_NUMERICAL_LITERAL": return type_ast_numerical_literal(ast, context)
    elif ast_type == "EXPRESSION_OPERATOR":           return type_ast_expression_operator(ast, context, propagation)
    elif ast_type == "FUNCTION_CALL":                 return type_ast_function_call(ast, context, propagation)
    else:                                             print("Error!")



# Function to process type declarations and add them to the typing context (Γ).
def process_type_declarations(ast: dict[str:any], Γ: _context) -> dict[str:_type]:
    types = {node["IDENTIFIER"]: node["LOGIC"] for node in filter(lambda node: node["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])}
    for k, v in types.items(): Γ = Γ + (k, type_create_singular(lambda val = v: form_expression(val)))
    return Γ



# Function to typecheck a type assignment/let statement.
def typecheck_type_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    if(statement["IDENTIFIER"] in Γ): raise Exception("Type Assignment (identifier already has a type!)")
    if((assigned_type := get_type_from_context(Γ, statement["ASSIGNED_TYPE"])) == None): raise Exception("Type",statement["ASSIGNED_TYPE"],"not in context:",Γ)
    debug(f"Let ::", statement["IDENTIFIER"], "is valid.")
    return add_type_to_context(Γ, statement["IDENTIFIER"], assigned_type), add_type_to_context(Ψ, statement["IDENTIFIER"], assigned_type)



# Function to typecheck a value assignment/set statement.
def typecheck_value_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    if((expr := type_ast_expression(statement["EXPRESSION"], Γ, Ψ)) < get_type_from_context(Γ, statement["IDENTIFIER"])):
        debug(f"Set ::", statement["IDENTIFIER"], "is valid.")
        return Γ, Ψ + (statement["IDENTIFIER"], expr)
    else:
        raise Exception("Invalid Set Statement :: Expression is not a subtype of asignee:", statement["IDENTIFIER"], " (", expr.logic.constraint()," : ", get_type_from_context(Γ, statement["IDENTIFIER"]).logic.constraint(), ")")


# Function to typecheck a function call.
def typecheck_function_call(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    try:
        T_FuncCall([type_ast_expression(arg["VALUE"], Γ, Ψ) for arg in statement["ARGUMENTS"]], get_type_from_context(Γ, statement["IDENTIFIER"]))
        debug(f"Function Call to", statement["IDENTIFIER"], "is valid.")
    except:
        print("Function Call to", statement["IDENTIFIER"]," :: Parameter Type Failure")
        for arg in statement["ARGUMENTS"]:
            print("\t" + arg["VALUE"]["IDENTIFIER"] + " : " + str(type_ast_expression(arg["VALUE"], Γ, Ψ).logic.constraint()))

    return Γ, Ψ 


 
def desugar_do_statement(statement: dict[str:any], Γ: _context, Ψ: _context):
    statements = []
    identifier = "anon"

    expr = type_ast_expression(statement["EXPRESSION"], Γ, Ψ)
    print(expr.logic.constraint())


    assignment = {
        "TYPE" : "TYPE_ASSIGNMENT",
        "IDENTIFIER" : identifier,
        "ASSIGNED_TYPE" : "Numerical"
    }

    assignment2 = {
        "TYPE" : "VALUE_ASSIGNMENT",
        "IDENTIFIER" : identifier,
        "EXPRESSION" : statement["EXPRESSION"]
    }
    
    statements.append(assignment)
    statements.append(assignment2)

    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        if_statement = {
            "TYPE" : "IF_STATEMENT",
            "EXPRESSION" : {
                "DATATYPE" : "OPERATOR",
                "DATA" : "==",
                "LEFT" : {
                    "DATATYPE" : "IDENTIFIER",
                    "DATA" : identifier
                },
                "RIGHT" : {
                    "DATATYPE" : ("NUMERICAL_LITERAL"),
                    "DATA" : on_statement["MATCH_VALUE"]
                }},
            "MATCH_COMMANDS" : on_statement["MATCH_COMMANDS"]
        }
        statements.append(if_statement)
        
    return statements, Γ, Ψ

    

def z3_to_python(expr, identifier):
    print(expr, str(type(expr)))
    if isinstance(expr, bool):
        return expr
    elif type(expr) == z3.RatNumRef:
            return {
                "EXPRESSION": {
                    "TYPE": "EXPRESSION_NUMERICAL_LITERAL",
                    "VALUE": str(expr)
                }
            }
    elif is_not(expr):
        return f"not {z3_to_python(expr.children()[0], identifier)}"

    elif is_gt(expr) or is_ge(expr) or is_lt(expr) or is_le(expr) or is_or(expr) or is_and(expr) or is_implies(expr):
        operator = ""
        if is_gt(expr):
            operator = ">"
        elif is_ge(expr):
            operator = ">="
        elif is_lt(expr):
            operator = "<"
        elif is_le(expr):
            operator = "<="
        elif is_or(expr):
            operator = "v"
        elif is_and(expr):
            operator = "^"
        elif is_implies(expr):
            operator = "==>"
            
        return {
            "EXPRESSION": {
                "TYPE": "EXPRESSION_OPERATOR",
                "IDENTIFIER": operator,
                "LEFT": z3_to_python(expr.children()[0], identifier)["EXPRESSION"],
                "RIGHT": z3_to_python(expr.children()[1], identifier)["EXPRESSION"]
            }
        }

    else:
        return {
                "EXPRESSION" : {
						"TYPE" : "EXPRESSION_IDENTIFIER",
						"IDENTIFIER" : identifier
                        }
        }   


def desugar_trycast_statement(trycast_statement: dict[str:any], Γ: _context, Ψ: _context):
    dom, cast = trycast_statement["DOMINANT_IDENTIFIER"], trycast_statement["CASTED_IDENTIFIER"]
    dom_t, cast_t = get_type_from_context(Γ, dom), get_type_from_context(Γ, cast)
    debug(f"Trycast {(dom_t.logic.constraint())} into {(cast_t.logic.constraint())}")
    statements = []
    identifier = "anon2"

    assignment = {
        "TYPE" : "TYPE_ASSIGNMENT",
        "IDENTIFIER" : "anon2",
        "ASSIGNED_TYPE" : "Numerical"
    }

    expr = z3_to_python(cast_t.logic.constraint(), trycast_statement["DOMINANT_IDENTIFIER"])["EXPRESSION"]

    assignment2 = {
        "TYPE" : "VALUE_ASSIGNMENT",
        "IDENTIFIER" : "anon2",
        "EXPRESSION" :  expr
    }

    print(json.dumps(assignment2, indent=4))
    
    statements.append(assignment)
    statements.append(assignment2)

    for index, on_statement in enumerate(trycast_statement["ON_STATEMENTS"]):

        if(on_statement["MATCH_VALUE"] not in [0, 1]):
            print("Invalid Trycast")
        else:
            print("Valid trycast")

        if_statement = {
            "TYPE" : "IF_STATEMENT",
            "EXPRESSION" : {
                "DATATYPE" : "OPERATOR",
                "DATA" : "==",
                "LEFT" : {
                    "DATATYPE" : "IDENTIFIER",
                    "DATA" : identifier
                },
                "RIGHT" : {
                    "DATATYPE" : "NUMERICAL_LITERAL",
                    "DATA" : on_statement["MATCH_VALUE"]
                }},
            "MATCH_COMMANDS" : on_statement["MATCH_COMMANDS"]
        }
        
        Γi, Ψi = duplicate_context(Γ), duplicate_context(Ψ)

        if on_statement["MATCH_VALUE"] == 1:
            print("TRYCAST :: Success Matching Found!")
            print("Assigning ", dom, " as type ", cast_t.logic.constraint(), " under psi")
            Ψi = Ψi + (dom, cast_t)
            typecheck_if_statement(if_statement, Γi, Ψi)

        if on_statement["MATCH_VALUE"] == 0:
            print("TRYCAST :: Failure Matching Found!")
        
        statements.append(if_statement)
    
    return statements, Γ, Ψ



def typecheck_if_statement(if_statement: dict[str:any], Γ: _context, Ψ: _context):

    print(if_statement["EXPRESSION"])
    expr = form_expression(if_statement["EXPRESSION"])
    
    index = 0
    while index < len(if_statement["MATCH_COMMANDS"]):
        statement = if_statement["MATCH_COMMANDS"][index]
        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT": Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)
        if statement["TYPE"] == "DO_STATEMENT":
            statements, Γ, Ψ = desugar_do_statement(statement, Γ, Ψ)
            if_statement["MATCH_COMMANDS"][index:index + 1] = statements
            continue
        if statement["TYPE"] == "IF_STATEMENT":     Γ, Ψ = typecheck_if_statement(statement, Γ, Ψ)
        if statement["TYPE"] == "TRYCAST_STATEMENT":
            desugar_trycast_statement(statement, Γ, Ψ)
            continue
        index = index + 1
    return Γ, Ψ 

# Function to type check a Function Declaration.
def typecheck_function(function: dict[str:any], Γ: _context):

    # Binding Base Types and `return` function type.
    Ψ = context_create('Ψ')
    Γ = Γ + ("Integer", type_create_singular(lambda: True)) 
    Γ = Γ + ("return", type_create_function([get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint], get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint))

    
    for index, input in enumerate(function["INPUTS"]):
        Γ = Γ + (function["ARGUMENTS"][index], get_type_from_context(Γ, input["TYPE"]))
        Ψ = Ψ + (function["ARGUMENTS"][index], get_type_from_context(Γ, input["TYPE"]))

    index = 0
    while index < len(function["BODY"]):
        statement = function["BODY"][index]
        print("Validating Statement of type: " + statement["TYPE"])

        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT": Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)
        if statement["TYPE"] == "IF_STATEMENT":     Γ, Ψ = typecheck_if_statement(statement, Γ, Ψ)

        if statement["TYPE"] == "DO_STATEMENT":
            statements, Γ, Ψ = desugar_do_statement(statement, Γ, Ψ)
            function["BODY"][index:index+1] = statements
            index += len(statements) - 1

        if statement["TYPE"] == "TRYCAST_STATEMENT":
            statements, Γ, Ψ = desugar_trycast_statement(statement, Γ, Ψ)
            function["BODY"][index:index+1] = statements
            index += len(statements) - 1

        index = index + 1
    return Ψ, Γ

            




def process_function_declarations(ast: dict[str:any], context: _context) -> _context:
    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:
        context = context + (function["IDENTIFIER"], type_create_function([get_type_from_context(context, type_identifier["TYPE"]).logic.constraint for type_identifier in function["INPUTS"]], get_type_from_context(context, function["RETURN_TYPE"]).logic.constraint))
        for doc in function["DOCSECTION"]:
            flags: list[str] = []
            if "FLAG" in doc: flags.append(doc["FLAG"])
        # file = parse_json_file("config.json")
        # if len(set(file["ENFORCED"]).difference(set(flags))) > 0:
        #    print("Failed enforced!")
        # else:
        #    print("Passed Enforced Flags!")

    return context



# Function to type check an AST
def typecheck_ast(ast: dict[str:any]):
    Γ = context_create('Γ')
    Γ = Γ + ("Integer", type_create_singular(lambda: True)) 
    Γ = Γ + ("Numerical", type_create_singular(lambda: True)) 

    Γ = process_type_declarations(ast, Γ)
    Γ = process_function_declarations(ast, Γ)

    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:
        print("Typechecking", function["IDENTIFIER"])
        typecheck_function(function, duplicate_context(Γ))

    


def main():
    parser = argparse.ArgumentParser(description='Program to compile MPIR AST File (JSON) to LaTeX.')

    # Add support for version option
    parser.add_argument('-V', '--version', action='version', version='%(prog)s 1.0')
    parser.add_argument('-i', '--input', metavar='input_file', type=str, nargs='?', help='input file path', default='testj.json')
    parser.add_argument('-o', '--output', dest='output_file', metavar='output_file', type=str, help='output file path', default='default_output.py')
    parser.add_argument('-c', '--config', metavar='config_file', type=str, help='config file path')
    args = parser.parse_args()

    input_file = args.input
    output_file = args.output_file
    config_file = args.config

    # Your code to process input_file and output_file goes here
    print("Input file:", input_file)
    print("Output file:", output_file)

    ast = parse_json_file(input_file)
    typecheck_ast(ast)
    build_python(ast, output_file)


if __name__ == "__main__":
    main()