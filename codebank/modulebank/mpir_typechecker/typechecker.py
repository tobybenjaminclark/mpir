import z3
import argparse
from typing_context import *
from typing_context import _type, _context, _function_type
from core_calculus import *
from mpir_module_python import build_python
from mpir_module_tex import build_tex
from typing import Literal, IO
import json
import traceback
import copy
import string
import random

g_errors = []

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
        ">": lambda: left > right, "≥": lambda: left >= right, "<": lambda: left < right, "≤": lambda: left <= right, "=": lambda: left == right, "==": lambda: left == right, "%": lambda: left % right,
 
        ">=": lambda: left >= right, "<=": lambda: left <= right, "v": lambda: z3.Or(left, right),
        
        # Negation, Conjunction & Disjunction
        "∧": lambda:z3.And(left, right), "∨": lambda: z3.Or(left, right), "¬": lambda: z3.Not(left), "/": lambda: left / right, "*": lambda: left * right, "+": lambda: left + right, "-": lambda: left - right,

        # Predicates (Forall, Exists)
        "∀": lambda: z3.ForAll(left, right), "∃": lambda: z3.Exists(left, right),
    }
    return operator_mapping.get(operator, lambda: None)()



# Converts an expression to Z3 logic.
def form_expression(type_logic: dict, symbol:chr = 'σ'):
    match type_logic["TYPE"]:
        case "EXPRESSION_OPERATOR":            return convert_operator_to_z3(type_logic["IDENTIFIER"], form_expression(type_logic["LEFT"], symbol), form_expression(type_logic["RIGHT"], symbol))
        case "EXPRESSION_IDENTIFIER":          return z3.Real(symbol)
        case "EXPRESSION_NUMERICAL_LITERAL":   return z3.RealVal(type_logic["VALUE"])
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
    arguments = []
    for arg in ast["ARGUMENTS"]:
        context, propagation, a = substitute_expression(arg["VALUE"], context, propagation)
        arguments.append(a)
    T_FuncCall(arguments, ast, context, propagation)
    debug(f"Function Call to", ast["IDENTIFIER"], "is valid.")
    
    func_ref = get_type_from_context(context, ast["IDENTIFIER"])
    letters = string.ascii_letters
    a = ( ''.join(random.choice(letters) for i in range(10)) )
    b = Real(a)

    constr = substitute(func_ref.logic.output_constraint(), (σ, b))
    propagation = propagation + (a, type_create_singular(lambda: constr))

    return context, propagation, b


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
    for k, v in types.items(): Γ = Γ + (k, type_create_singular(lambda val = v: form_expression(val, 'σ')))
    return Γ



# Function to typecheck a type assignment/let statement.
def typecheck_type_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    if(statement["IDENTIFIER"] in Γ): raise Exception("Type Assignment (identifier already has a type!)")
    if((assigned_type := get_type_from_context(Γ, statement["ASSIGNED_TYPE"])) == None): raise Exception("Type",statement["ASSIGNED_TYPE"],"not in context:",Γ)
    debug(f"Let ::", statement["IDENTIFIER"], "is valid.")
    return add_type_to_context(Γ, statement["IDENTIFIER"], assigned_type), add_type_to_context(Ψ, statement["IDENTIFIER"], assigned_type)



def substitute_expression(ast: dict[str:any], Γ: _context, Ψ: _context) -> z3.ExprRef:
    ast_type = ast["TYPE"]
    print("SUBSTITUTE")
    print(ast)
    print(ast_type)
    print("\n")
    
    if ast_type   == "EXPRESSION_IDENTIFIER":
        iden = Real(ast["IDENTIFIER"])
        return Γ, Ψ, (lambda: iden)()
    elif ast_type ==  "EXPRESSION_NUMERICAL_LITERAL":
        return Γ, Ψ, (lambda: RealVal(float(ast["VALUE"])))()
    elif ast_type == "EXPRESSION_OPERATOR":
        Γ, Ψ, left = substitute_expression(ast["LEFT"], Γ, Ψ)
        Γ, Ψ, right = substitute_expression(ast["RIGHT"], Γ, Ψ)
        return Γ, Ψ, convert_operator_to_z3(ast["IDENTIFIER"], left, right)
    elif ast_type == "FUNCTION_CALL":
        return type_ast_function_call(ast, Γ, Ψ)
    else:
        print("Error!")



# Function to typecheck a value assignment/set statement.
def typecheck_value_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    print("Typechecking Value Assignment of ", statement["IDENTIFIER"])
    Γ, Ψ, expr = substitute_expression(statement["EXPRESSION"], Γ, Ψ)
    solver = z3.Solver()
    sigma = Real('σ')

    for iden, typ in Γ:
        if isinstance(typ.logic, _function_type): continue
        iden_s = Real(iden)
        expr2 = substitute(typ.logic.constraint(), (sigma, iden_s))
        solver.add(expr2)

    for iden, typ in Ψ:
        if isinstance(typ.logic, _function_type): continue
        print("Ψ: iden", typ.logic.constraint())
        iden_s = Real(iden)
        expr2 = substitute(typ.logic.constraint(), (sigma, iden_s))
        solver.add(expr2)

    temp22 = Real("temp22")
    typ2 = get_type_from_context(Γ, statement["IDENTIFIER"])
    solver.add(temp22 == expr)
    
    e_typ = get_type_from_context(Ψ, statement["IDENTIFIER"])
    remove_type_from_context(Ψ, statement["IDENTIFIER"])

    Ψ = Ψ + (statement["IDENTIFIER"], type_create_singular(lambda: z3.And(sigma == expr, e_typ.logic.constraint())))

    constr = substitute(typ2.logic.constraint(), (sigma, temp22))

    solver.add(z3.Not(constr))
    print(solver)
    if solver.check() == z3.sat:
        print("SAT")
        model = solver.model()
        print(model)
        raise Exception()
    else:
        print("UNSAT")
        remove_type_from_context(Ψ, statement["IDENTIFIER"])
        test = Real(statement["IDENTIFIER"])
        Ψ = Ψ + (statement["IDENTIFIER"], type_create_singular(lambda: test == expr))

    
    return Γ, Ψ


# Function to typecheck a function call.
def typecheck_function_call(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    arguments = []
    for arg in statement["ARGUMENTS"]:
        Γ, Ψ, a = substitute_expression(arg["VALUE"], Γ, Ψ)
        arguments.append(a)
    T_FuncCall(arguments, statement, Γ, Ψ)
    debug(f"Function Call to", statement["IDENTIFIER"], "is valid.")

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
                "TYPE" : "EXPRESSION_OPERATOR",
                "IDENTIFIER" : "==",
                "LEFT" : {
                    "TYPE" : "IDENTIFIER",
                    "IDENTIFIER" : identifier
                },
                "RIGHT" : {
                    "TYPE" : ("EXPRESSION_NUMERICAL_LITERAL"),
                    "VALUE" : on_statement["MATCH_VALUE"]
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


def desugar_trycast_statement(trycast_statement: dict[str:any], Γ: _context, Ψ: _context, ast, assigned_variables, index):
    dom, cast = trycast_statement["DOMINANT_IDENTIFIER"], trycast_statement["CASTED_IDENTIFIER"]
    dom_t, cast_t = get_type_from_context(Γ, dom), get_type_from_context(Γ, cast)

    if(dom_t is None): raise Exception("Trycast: " + trycast_statement["DOMINANT_IDENTIFIER"] + " is not defined under Γ")
    if(cast_t is None): raise Exception("Trycast: " + trycast_statement["CASTED_IDENTIFIER"] + " is not defined under Γ")

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

    if len([o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]]) != 2: raise Exception("Not enough on statements in trycast.")
    elif 0 not in [o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]] or 1 not in [o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]]: raise Exception("Trycast on statements missing 1/0 control-flow")

    for index, on_statement in enumerate(trycast_statement["ON_STATEMENTS"]):

        if(on_statement["MATCH_VALUE"] not in [0, 1]): print("Invalid Trycast")
        else: print("Valid trycast")
            
        if on_statement["MATCH_VALUE"] == 1:
            cmd = on_statement["MATCH_COMMANDS"]

            dom_success = dom + "_succ"
            iden_s = Real(dom_success)
            
            print("Doing it for success case")
            print(cmd)
            cmd = ast_substitute(cmd, dom, dom_success)[0]
            print(cmd)

            sigma = Real('σ')

            cast_t_copy = copy.deepcopy(cast_t)
            substitute(cast_t_copy.logic.constraint(), (sigma, iden_s))
            t = type_create_singular(lambda: cast_t_copy.logic.constraint())
            print("Assigning ", dom_success, " as type ", t.logic.constraint(), " under psi")
            Γ = Γ + (dom_success, t)
            Ψ = Ψ + (dom_success, t)
            print(Ψ)
            
            if cmd["IDENTIFIER"] not in assigned_variables:
                assigned_variables.append(cmd["IDENTIFIER"])
                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)
            else:
                old_name = cmd["IDENTIFIER"]
                new_name = cmd["IDENTIFIER"] + "I"
                while new_name in assigned_variables:
                    new_name = new_name + "I"
                assigned_variables.append(new_name)

                index2 = index + 1

                ast_substitute(ast["BODY"][index + 1:], cmd["IDENTIFIER"], new_name)
                ast["BODY"][index]["IDENTIFIER"] = new_name
                print(json.dumps(ast["BODY"], indent = 4))
                
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)

        elif on_statement["MATCH_VALUE"] == 0:
            cmd = on_statement["MATCH_COMMANDS"]

            dom_fail = dom + "_fail"
            iden_s = Real(dom_fail)

            print("Doing it for fail case")
            print(cmd)
            cmd = ast_substitute(cmd, dom, dom_fail)[0]
            print(cmd)

            sigma = Real('σ')

            dom_t_copy = copy.deepcopy(dom_t)
            substitute(dom_t_copy.logic.constraint(), (sigma, iden_s))
            t = type_create_singular(lambda: dom_t_copy.logic.constraint())
            print("Assigning", dom_fail, "as type", t.logic.constraint(), " under psi!")
            Γ = Γ + (dom_fail, t)
            Ψ = Ψ + (dom_fail, t)
            print(Ψ)
            
            if cmd["IDENTIFIER"] not in assigned_variables:
                assigned_variables.append(cmd["IDENTIFIER"])
                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)
            else:
                old_name = cmd["IDENTIFIER"]
                new_name = cmd["IDENTIFIER"] + "I"
                while new_name in assigned_variables:
                    new_name = new_name + "I"
                assigned_variables.append(new_name)

                index2 = index + 1
                print("Substituting all values of ", cmd["IDENTIFIER"], " with ", new_name)

                ast_substitute(ast["BODY"][index + 1:], cmd["IDENTIFIER"], new_name)
                ast["BODY"][index]["IDENTIFIER"] = new_name
                print(json.dumps(ast["BODY"], indent = 4))
                
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)

    print("returned propagational context of: \n", Ψ)
    return Γ, Ψ



def typecheck_if_statement(if_statement: dict[str:any], Γ: _context, Ψ: _context, ast, assigned_variables):

    print(if_statement["EXPRESSION"])
    expr = form_expression(if_statement["EXPRESSION"], 'σ')
    
    print("IF STATEMENT CONTEXTS:")
    print(Γ)
    print(Ψ)

    index = 0
    while index < len(if_statement["MATCH_COMMANDS"]):
        statement = if_statement["MATCH_COMMANDS"][index]
        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT":
                Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)

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

# Function to substitute variables in a Function Declaration
def ast_substitute(d, old_str, new_str) -> list[any]:
    if isinstance(d, dict):
        for key, value in d.items():
            d[key] = ast_substitute(value, old_str, new_str)
        return d
    elif isinstance(d, str):
        return d.replace(old_str, new_str)
    elif isinstance(d, list):
        return [ast_substitute(item, old_str, new_str) for item in d]
    else:
        return d  # No replacement needed for non-string values

# Function to type check a Function Declaration.
def typecheck_function(function: dict[str:any], Γ: _context):

    # Binding Base Types and `return` function type.
    Ψ = context_create('Ψ')
    σ = Real('σ')
    Γ = Γ + ("Integer", type_create_singular(lambda: z3.And(σ > -2147483648, σ < 2147483648))) 
    Γ = Γ + ("return", type_create_function([get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint], get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint))
    
    for index, input in enumerate(function["INPUTS"]):
        print(function["ARGUMENTS"][index], " :: ",input)
        test = Real(function["ARGUMENTS"][index])
        Γ = Γ + (function["ARGUMENTS"][index], type_create_singular(lambda: substitute(get_type_from_context(Γ, input["TYPE"]).logic.constraint(), (σ, test))))
        Ψ = Ψ + (function["ARGUMENTS"][index], type_create_singular(lambda: substitute(get_type_from_context(Γ, input["TYPE"]).logic.constraint(), (σ, test))))
    print(Γ)

    assigned_variables = []

    index = 0
    while index < len(function["BODY"]):
        
        statement = function["BODY"][index]
        print("Validating Statement of type: " + statement["TYPE"])

        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT":
            
            # Append to assigned variables
            if statement["IDENTIFIER"] not in assigned_variables:
                assigned_variables.append(statement["IDENTIFIER"])
                Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)

            else:
                # Convert to SSA
                old_name = statement["IDENTIFIER"]
                new_name = statement["IDENTIFIER"] + "I"
                while new_name in assigned_variables:
                    new_name = new_name + "I"
                assigned_variables.append(new_name)

                index2 = index + 1
                print("Substituting all values of ", statement["IDENTIFIER"], " with ", new_name)

                ast_substitute(function["BODY"][index + 1:], statement["IDENTIFIER"], new_name)
                function["BODY"][index]["IDENTIFIER"] = new_name
                print(json.dumps(function["BODY"], indent = 4))
                
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)

                print(Γ)
                print(Ψ)
                print(statement["IDENTIFIER"])

            print(assigned_variables, "\n")
            

            
        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)
        if statement["TYPE"] == "IF_STATEMENT":
            Γ, Ψ = typecheck_if_statement(statement, Γ, Ψ, function, assigned_variables)

        if statement["TYPE"] == "DO_STATEMENT":
            statements, Γ, Ψ = desugar_do_statement(statement, Γ, Ψ)
            function["BODY"][index:index+1] = statements
            index += len(statements) - 1

        if statement["TYPE"] == "TRYCAST_STATEMENT":
            Γ, Ψ = desugar_trycast_statement(statement, Γ, Ψ, function, assigned_variables, index)

        index = index + 1
    return Ψ, Γ

            




def process_function_declarations(ast: dict[str:any], context: _context) -> _context:
    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:
        for type_identifier in function["INPUTS"]:
            a = get_type_from_context(context, type_identifier["TYPE"])
            if a == None:
                print("Type doesn't exist :: ", type_identifier)

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
    σ = z3.Real('σ')
    Γ = Γ + ("Integer", type_create_singular(lambda: z3.And(σ > -2147483648, σ < 2147483648)))
    Γ = Γ + ("Numerical", type_create_singular(lambda: z3.And(σ > -2147483648, σ < 2147483648)))

    Γ = process_type_declarations(ast, Γ)
    print(Γ)
    Γ = process_function_declarations(ast, Γ)

    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:

        print("Typechecking", function["IDENTIFIER"])
        typecheck_function(function, duplicate_context(Γ))
        continue

        try:
            typecheck_function(function, duplicate_context(Γ))
        except Exception as e:
            print(traceback.format_exc())
            raise Exception("Error typechecking function: " + function["IDENTIFIER"])

            g_errors.append(str(e))
    
    return Γ
    


def main():
    parser = argparse.ArgumentParser(description='Program to compile MPIR AST File (JSON) to LaTeX.')

    # Add support for version option
    parser.add_argument('-V', '--version', action='version', version='%(prog)s 1.0')
    parser.add_argument('-i', '--input', metavar='input_file', type=str, nargs='?', help='input file path', default='codebank/modulebank/testj.json')
    parser.add_argument('-o', '--output', dest='output_file', metavar='output_file', type=str, help='output file path', default='output.tex')
    parser.add_argument('-c', '--config', metavar='config_file', type=str, help='config file path')
    args = parser.parse_args()

    input_file = args.input
    output_file = args.output_file
    config_file = args.config

    # Your code to process input_file and output_file goes here
    ast = parse_json_file(input_file)
    Γ = typecheck_ast(ast)

    print(f"Writing to {output_file} {len(g_errors)}")
    if(output_file.endswith(".py")):
        if len(g_errors) == 0: build_python(ast, output_file, Γ)
        else:
            with open(output_file, 'w') as file:
                for item in g_errors:
                    file.write("# " + str(item) + '\n')
            print("Array contents written to", output_file)
    elif(output_file.endswith(".tex")):
        if len(g_errors) == 0: build_tex(ast, output_file, Γ)
        else:# Open the file for writing
            with open(output_file, 'w') as file:
                # Write each element of the array to the file
                for item in g_errors:
                    file.write("# " + str(item) + '\n')
        print("Array contents written to", output_file)


if __name__ == "__main__":
    main()