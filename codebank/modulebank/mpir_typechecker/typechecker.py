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

ssa_mapping = {}
g_errors = []


def ssa_get_origin(identifier):
    """ Function to replace origin of SSA. """
    while identifier in ssa_mapping: identifier = ssa_mapping[identifier]
    return identifier


def ssa_replace(node, old_str, new_str) -> list[any]:
    """Function to substitute variables in a Function Declaration"""
    ssa_mapping[new_str] = old_str
    if isinstance(node, dict):
        for key, value in node.items(): node[key] = ssa_replace(value, old_str, new_str)
    elif isinstance(node, str):         node = new_str if node == old_str else node
    elif isinstance(node, list):        node = [ssa_replace(item, old_str, new_str) for item in node]
    return node


def ssa_revert(node:any) -> any:
    """ Function to substitute variables in a Function Declaration """
    if isinstance(node, dict):
        for key, value in node.items(): node[key] = ssa_revert(value)
    elif isinstance(node, str):         node = ssa_get_origin(node)
    elif isinstance(node, list):        node = [ssa_revert(item) for item in node]
    return node


def parse_json_file(filename: str) -> dict|None:
    """Function to parse JSON given a file, filename."""
    try:
        file = open(filename, 'r')
        data = json.load(file)
        file.close()
        return data
    except FileNotFoundError:
        return None
    except json.JSONDecodeError as e:
        return None



DEBUG_MODE = True

def debug(*args, sep: str | None = " ", end: str | None = "\n", flush: Literal[False] = False) -> None:
    """Prints a debug message if in debug mode."""
    return print(">>",*args, sep = sep, end = end, flush = flush) if DEBUG_MODE else None



def convert_operator_to_z3(operator: str, left, right):
    """Converts an operator node to Z3 logic."""
    operator_mapping = {
        # Comparators
        ">": lambda: left > right, "≥": lambda: left >= right, "<": lambda: left < right, "≤": lambda: left <= right, "=": lambda: left == right, "==": lambda: left == right, "%": lambda: left % right,
 
        ">=": lambda: left >= right, "<=": lambda: left <= right, "v": lambda: z3.Or(left, right), "^": lambda:z3.And(left, right),
        
        # Negation, Conjunction & Disjunction
        "∧": lambda:z3.And(left, right), "∨": lambda: z3.Or(left, right), "¬": lambda: z3.Not(left), "/": lambda: left / right, "*": lambda: left * right, "+": lambda: left + right, "-": lambda: left - right,

        # Predicates (Forall, Exists)
        "∀": lambda: z3.ForAll(left, right), "∃": lambda: z3.Exists(left, right),
    }
    if operator not in operator_mapping:
        raise Exception("Operator not found: " + str(operator))
    return operator_mapping.get(operator, lambda: None)()



def form_expression(type_logic: dict, symbol:chr = 'σ'):
    """Converts an expression to Z3 logic."""
    match type_logic["TYPE"]:
        case "EXPRESSION_OPERATOR":            return convert_operator_to_z3(type_logic["IDENTIFIER"], form_expression(type_logic["LEFT"], symbol), form_expression(type_logic["RIGHT"], symbol))
        case "EXPRESSION_IDENTIFIER":          return z3.Real(symbol)
        case "EXPRESSION_NUMERICAL_LITERAL":   return z3.RealVal(type_logic["VALUE"])
        case _:
            raise Exception("Can't process " + str(type_logic))




def type_ast_expression_operator(ast, context, propagation, σ=z3.Real('σ')) -> _type:
    """Function to infer the type of an expression operator node, from the types of it's constituents."""
    op_mapping = {"+": T_Add, "*": T_Mult, "-": T_Sub, "/": T_Div,
                  ">": T_Comp, ">=": T_Comp, "<": T_Comp, "<=": T_Comp, "^": T_Comp, "v": T_Comp}
    if ast["LEFT"]["TYPE"] == "EXPRESSION_IDENTIFIER" and ast["LEFT"]["IDENTIFIER"] not in propagation: raise Exception(f"Undeclared Identifier " + ast["LEFT"]["IDENTIFIER"])
    if ast["RIGHT"]["TYPE"] == "EXPRESSION_IDENTIFIER" and ast["RIGHT"]["IDENTIFIER"] not in propagation: raise Exception(f"Undeclared Identifier " + ast["RIGHT"]["IDENTIFIER"])
    return op_mapping.get(ast["IDENTIFIER"], lambda: print("Error!"))(
        type_ast_expression(ast["LEFT"], context, propagation),
        type_ast_expression(ast["RIGHT"], context, propagation)
    )



def type_ast_numerical_literal(ast, context, σ=z3.Real('σ')) -> _type:
    """Function to infer the type of a numerical literal."""
    return type_create_singular(lambda: σ == ast["VALUE"])




def type_ast_function_call(ast, context, propagation, σ=z3.Real('σ')) -> _type:
    """Function to Type Check a Function Call as part of an expression."""
    arguments = []
    for arg in ast["ARGUMENTS"]:
        context, propagation, a = substitute_expression(arg["VALUE"], context, propagation)
        arguments.append(a)
    
    # Try and check the function call, make sure it's okay.
    try: T_FuncCall(arguments, ast, context, propagation)
    except Exception as e: raise Exception("Error on line: " + str(e.args[0]["line"]) + ", on call to " +  ssa_get_origin(e.args[0]["iden"]) + ". Possible invalidity of arg " + ssa_get_origin(e.args[0]["arg"]) + " (" + e.args[0]["conflict"] + ")")

    # Encapsulate the function call as a new identifier
    func_ref = get_type_from_context(context, ast["IDENTIFIER"])
    letters = string.ascii_letters
    a = ( ''.join(random.choice(letters) for i in range(15)) )
    b = Real(a)

    constr = substitute(func_ref.logic.output_constraint(), (σ, b))
    propagation = propagation + (a, type_create_singular(lambda: constr))

    return context, propagation, b



def type_ast_expression(ast, context, propagation, σ = z3.Real('σ')) -> _type:
    """Function to infer the type of an ast expression."""
    ast_type = ast["TYPE"]
    if ast_type   == "EXPRESSION_IDENTIFIER":         return get_type_from_context(propagation, ast["IDENTIFIER"])
    elif ast_type ==  "EXPRESSION_NUMERICAL_LITERAL": return type_ast_numerical_literal(ast, context)
    elif ast_type == "EXPRESSION_OPERATOR":           return type_ast_expression_operator(ast, context, propagation)
    elif ast_type == "FUNCTION_CALL":                 return type_ast_function_call(ast, context, propagation)
    else:                                             print("Error!")




def process_type_declarations(ast: dict[str:any], Γ: _context) -> dict[str:_type]:
    """Function to process type declarations and add them to the typing context (Γ)."""
    types = {node["IDENTIFIER"]: node["LOGIC"] for node in filter(lambda node: node["TYPE"] == "TYPE_DECLARATION", ast["CONTENTS"])}
    for k, v in types.items():
        typ = type_create_singular(lambda val = v: form_expression(val, 'σ'))
        Γ = Γ + (k, typ)
    return Γ



def typecheck_type_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    """Function to typecheck a type assignment/let statement."""
    if(statement["IDENTIFIER"] in Γ): raise Exception("Type Assignment (identifier already has a type!)")
    if((assigned_type := get_type_from_context(Γ, statement["ASSIGNED_TYPE"])) == None): raise Exception("Type",statement["ASSIGNED_TYPE"],"not in context:",Γ)
    debug(f"Let ::", statement["IDENTIFIER"], "is valid.")
    return add_type_to_context(Γ, statement["IDENTIFIER"], assigned_type), Ψ



def substitute_expression(ast: dict[str:any], Γ: _context, Ψ: _context) -> z3.ExprRef:
    """Function to convert an AST into z3 logic."""
    ast_type = ast["TYPE"]
    if ast_type   == "EXPRESSION_IDENTIFIER":
        iden = Real(ast["IDENTIFIER"])
        if get_type_from_context(Ψ, ast["IDENTIFIER"]) == None: raise Exception("Undeclared variable: " + ast["IDENTIFIER"])
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



def typecheck_value_assignment(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    """Function to typecheck a value assignment/set statement."""

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
    if solver.check() == z3.sat:
        model = solver.model()
        a = model.evaluate(temp22).as_decimal(3)
        raise Exception("Line " + str(statement["LINE"]) + " :: Invalid assignment, possible value of " + str(a))
    else:
        remove_type_from_context(Ψ, statement["IDENTIFIER"])
        test = Real(statement["IDENTIFIER"])
        Ψ = Ψ + (statement["IDENTIFIER"], type_create_singular(lambda: test == expr))

    
    return Γ, Ψ


def typecheck_function_call(statement: dict[str:any], Γ: _context, Ψ: _context) -> tuple[_context, _context]:
    """Function to typecheck a function call."""
    arguments = []
    for arg in statement["ARGUMENTS"]:
        Γ, Ψ, a = substitute_expression(arg["VALUE"], Γ, Ψ)
        arguments.append(a)
    
    try:
        T_FuncCall(arguments, statement, Γ, Ψ)
    except Exception as e:
        raise Exception("Error on line: " + str(e.args[0]["line"]) + ", on call to " + ssa_get_origin(e.args[0]["iden"]) + ". Possible invalidity of arg " + ssa_get_origin(e.args[0]["arg"]) + " (" + e.args[0]["conflict"] + ")")
    
    debug(f"Function Call to", statement["IDENTIFIER"], "is valid.")

    return Γ, Ψ 


 
def desugar_do_statement(statement: dict[str:any], Γ: _context, Ψ: _context, ast, assigned_variables, index):
    """Function to desugar a DOON statement into z3 logic."""
    solver = Solver()
    sigma = Real('σ')

    for iden, typ in Γ:
        if isinstance(typ.logic, _function_type): continue
        iden_s = Real(iden)
        expr2 = substitute(typ.logic.constraint(), (sigma, iden_s))
        solver.add(expr2)

    for iden, typ in Ψ:
        if isinstance(typ.logic, _function_type): continue
        iden_s = Real(iden)
        expr2 = substitute(typ.logic.constraint(), (sigma, iden_s))
        solver.add(expr2)

    temp_identifier = ( ''.join(random.choice(string.ascii_letters) for i in range(15)) )
    temp_id = Real(temp_identifier)

    Γ, Ψ, expr = substitute_expression(statement["EXPRESSION"], Γ, Ψ)
    

    if (is_bool(expr)):
        solver.add(If(expr == True, temp_id == 1, temp_id == 0))
        Ψ = Ψ + (temp_identifier, type_create_singular(lambda: If(expr == True, temp_id == 1, temp_id == 0)))
    elif (is_real(expr)):
        solver.add(temp_id == expr)
        Ψ = Ψ + (temp_identifier, type_create_singular(lambda: temp_id == expr))
   
    # Now we have expression as a type, we can match it against literals.
    vars = {}
    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        cmd = on_statement["MATCH_COMMANDS"]
        iden = cmd[0]["IDENTIFIER"]
        new_name = (cmd[0]["IDENTIFIER"]) + "I"
        while new_name in assigned_variables:
            new_name = new_name + "I"
        cmd[0]["IDENTIFIER"] = new_name
        ssa_mapping[new_name] = iden
        assigned_variables.append(new_name)
        
        iden_og = get_type_from_context(Γ, iden)
        if iden_og == None:
            raise Exception("Variable undeclared! " + iden)
        iden_typ = copy.deepcopy(iden_og)
        Γ = Γ + (new_name, iden_typ)
        
        # So we know what ones to map back.
        if iden not in vars:
            vars[iden] = [(float(on_statement["MATCH_VALUE"]), new_name)]
        else:
            vars[iden].append((float(on_statement["MATCH_VALUE"]), new_name))

    for index, on_statement in enumerate(statement["ON_STATEMENTS"]):
        cmd = on_statement["MATCH_COMMANDS"]

        Γ, Ψ = typecheck_value_assignment(cmd[0], Γ, Ψ)

    # Now, convergae values under Psi function
    for k, v in vars.items():
        og_typ = get_type_from_context(Γ, k)
        new_name = k + "I"
        while new_name in assigned_variables:
            new_name = new_name + "I"
        ssa_replace(ast["BODY"][index + 1:], k, new_name)
        kval = Real('σ')

        def gen_if (_id, _kval, vals):
            if len(vals) == 0: return lambda: z3.BoolVal(True)

            v = vals.pop(0)
            matchval = RealVal(v[0])
            iden = Real(v[1])
            try:
                e = gen_if(_id, _kval, vals)()
                return lambda: If(_id == matchval, _kval == iden, e)
            except:
                print(_id)

        prop_typ = type_create_singular(gen_if(temp_id, kval, v))
        Γ = Γ + (new_name, og_typ)
        Ψ = Ψ + (new_name, prop_typ)

    return Γ, Ψ

    

def z3_to_python(expr, identifier):
    """Function to convert z3 logic to python."""
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
    """Function to desugar a TRYCAST statement and handle success / failure."""
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

    
    statements.append(assignment)
    statements.append(assignment2)

    if len([o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]]) != 2: raise Exception("Not enough on statements in trycast.")
    elif 0 not in [o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]] or 1 not in [o["MATCH_VALUE"] for o in trycast_statement["ON_STATEMENTS"]]: raise Exception("Trycast on statements missing 1/0 control-flow")

    if trycast_statement["ON_STATEMENTS"][0]["MATCH_COMMANDS"][0]["IDENTIFIER"] == trycast_statement["ON_STATEMENTS"][1]["MATCH_COMMANDS"][0]["IDENTIFIER"]:
        same = True
    else:
        same = False

    for on_statement in trycast_statement["ON_STATEMENTS"]:

        if(on_statement["MATCH_VALUE"] not in [0, 1]): print("Invalid Trycast")
        else: print("Valid trycast")
            
        if on_statement["MATCH_VALUE"] == 1:
            cmd = on_statement["MATCH_COMMANDS"]

            dom_success = dom + "_succ"
            iden_s = Real(dom_success)
            
            cmd = ssa_replace(cmd, dom, dom_success)[0]
            sigma = Real('σ')

            cast_t_copy = copy.deepcopy(cast_t)
            substitute(cast_t_copy.logic.constraint(), (sigma, iden_s))
            t = type_create_singular(lambda: cast_t_copy.logic.constraint())
            Γ = Γ + (dom_success, t)
            Ψ = Ψ + (dom_success, t)
            
            if cmd["IDENTIFIER"] not in assigned_variables:
                assigned_variables.append(cmd["IDENTIFIER"])
                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)
            else:
                old_name = cmd["IDENTIFIER"]
                new_name = cmd["IDENTIFIER"] + "I"
                while new_name in assigned_variables:
                    new_name = new_name + "I"
                assigned_variables.append(new_name)

                ssa_replace(ast["BODY"][index + 1:], cmd["IDENTIFIER"], new_name)
                cmd["IDENTIFIER"] = new_name
                
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)

        elif on_statement["MATCH_VALUE"] == 0:
            cmd = on_statement["MATCH_COMMANDS"]

            dom_fail = dom + "_fail"
            iden_s = Real(dom_fail)

            cmd = ssa_replace(cmd, dom, dom_fail)[0]

            sigma = Real('σ')

            dom_t_copy = copy.deepcopy(dom_t)
            substitute(dom_t_copy.logic.constraint(), (sigma, iden_s))
            t = type_create_singular(lambda: dom_t_copy.logic.constraint())
        
            Γ = Γ + (dom_fail, t)
            Ψ = Ψ + (dom_fail, t)
            
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
                ssa_replace(ast["BODY"][index + 1:], cmd["IDENTIFIER"], new_name)
                cmd["IDENTIFIER"] = new_name
                
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(cmd, Γ, Ψ)

    
    if same:
        name_og = trycast_statement["ON_STATEMENTS"][0]["MATCH_COMMANDS"][0]["IDENTIFIER"]
        new_name = name_og + "_combined"

        ssa_replace(ast["BODY"][index + 1:], name_og, new_name)
        ssa_replace(ast["BODY"][index + 1:], trycast_statement["ON_STATEMENTS"][1]["MATCH_COMMANDS"][0]["IDENTIFIER"], new_name)

        Γ = Γ + (new_name, get_type_from_context(Γ, name_og))

        typ1 = get_type_from_context(Ψ, trycast_statement["ON_STATEMENTS"][0]["MATCH_COMMANDS"][0]["IDENTIFIER"])
        typ2 = get_type_from_context(Ψ, trycast_statement["ON_STATEMENTS"][1]["MATCH_COMMANDS"][0]["IDENTIFIER"])
        typ1_copy = copy.deepcopy(typ1)
        typ2_copy = copy.deepcopy(typ2)

        new_id = Real(new_name)
        typ1_σ = Real(trycast_statement["ON_STATEMENTS"][0]["MATCH_COMMANDS"][0]["IDENTIFIER"])
        typ2_σ = Real(trycast_statement["ON_STATEMENTS"][1]["MATCH_COMMANDS"][0]["IDENTIFIER"])

        a = z3.substitute(typ1_copy.logic.constraint(), (typ1_σ, new_id))
        b = z3.substitute(typ2_copy.logic.constraint(), (typ2_σ, new_id))

        
        Ψ = Ψ + (new_name, type_create_singular(lambda: z3.Or(a, b)))
    return Γ, Ψ



def typecheck_if_statement(if_statement: dict[str:any], Γ: _context, Ψ: _context, ast, assigned_variables):
    """Function to typecheck an IF statement."""

    expr = form_expression(if_statement["EXPRESSION"], 'σ')
    

    index = 0
    while index < len(if_statement["MATCH_COMMANDS"]):
        statement = if_statement["MATCH_COMMANDS"][index]
        if statement["TYPE"] == "TYPE_ASSIGNMENT":  Γ, Ψ = typecheck_type_assignment(statement, Γ, Ψ)
        if statement["TYPE"] == "VALUE_ASSIGNMENT":
                Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)

        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)
        if statement["TYPE"] == "DO_STATEMENT":
            desugar_do_statement(statement, Γ, Ψ)
            continue
        if statement["TYPE"] == "IF_STATEMENT":     Γ, Ψ = typecheck_if_statement(statement, Γ, Ψ)
        if statement["TYPE"] == "TRYCAST_STATEMENT":
            desugar_trycast_statement(statement, Γ, Ψ)
            continue
        index = index + 1
    return Γ, Ψ 


def typecheck_function(function: dict[str:any], Γ: _context):
    """Function to type check a Function Declaration."""

    # Binding Base Types and `return` function type.
    Ψ = context_create('Ψ')
    σ = Real('σ')
    Γ = Γ + ("Integer", type_create_singular(lambda: z3.And(σ > -2147483648, σ < 2147483648))) 
    Γ = Γ + ("return", type_create_function([get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint], get_type_from_context(Γ, function["RETURN_TYPE"]).logic.constraint))
    
    for index, input in enumerate(function["INPUTS"]):
        test = Real(function["ARGUMENTS"][index])
        ityp = get_type_from_context(Γ, input["TYPE"])
        if(ityp == None): raise Exception(input["TYPE"] + " not declared under Γ!")
        Γ = Γ + (function["ARGUMENTS"][index], type_create_singular(lambda: substitute(ityp.logic.constraint(), (σ, test))))
        Ψ = Ψ + (function["ARGUMENTS"][index], type_create_singular(lambda: substitute(ityp.logic.constraint(), (σ, test))))

    assigned_variables = []

    index = 0
    while index < len(function["BODY"]):
        
        statement = function["BODY"][index]

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
                ssa_replace(function["BODY"][index + 1:], statement["IDENTIFIER"], new_name)
                function["BODY"][index]["IDENTIFIER"] = new_name
                gamma_t = get_type_from_context(Γ, old_name)
                psi_t = get_type_from_context(Ψ, old_name)
                Γ = Γ + (new_name, gamma_t)
                Ψ = Ψ + (new_name, psi_t)

                Γ, Ψ = typecheck_value_assignment(statement, Γ, Ψ)

            

            
        if statement["TYPE"] == "FUNCTION_CALL":    Γ, Ψ = typecheck_function_call(statement, Γ, Ψ)
        if statement["TYPE"] == "IF_STATEMENT":
            Γ, Ψ = typecheck_if_statement(statement, Γ, Ψ, function, assigned_variables)

        if statement["TYPE"] == "DO_STATEMENT":
            Γ, Ψ = desugar_do_statement(statement, Γ, Ψ, function, assigned_variables, index)
        if statement["TYPE"] == "TRYCAST_STATEMENT":
            Γ, Ψ = desugar_trycast_statement(statement, Γ, Ψ, function, assigned_variables, index)

        index = index + 1
    return Ψ, Γ

            




def process_function_declarations(ast: dict[str:any], context: _context) -> _context:
    """Function to process function declarations in the AST."""
    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:
        for type_identifier in function["INPUTS"]:
            a = get_type_from_context(context, type_identifier["TYPE"])
            if a == None:
                print("Type doesn't exist :: ", type_identifier)

        context = context + (function["IDENTIFIER"], type_create_function([get_type_from_context(context, type_identifier["TYPE"]).logic.constraint for type_identifier in function["INPUTS"]], get_type_from_context(context, function["RETURN_TYPE"]).logic.constraint))
        for doc in function["DOCSECTION"]:
            flags: list[str] = []
            if "FLAG" in doc: flags.append(doc["FLAG"])

    return context



def typecheck_ast(ast: dict[str:any]):
    """Function to type check an AST"""
    Γ = context_create('Γ')
    σ = z3.Real('σ')
    Γ = Γ + ("Integer", type_create_singular(lambda: z3.And(σ > -2147483648, σ < 2147483648)))
    Γ = Γ + ("Numerical", type_create_singular(lambda: z3.Bool(True)))

    Γ = process_type_declarations(ast, Γ)
    Γ = process_function_declarations(ast, Γ)
    
    for function in [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]:
        try:
            typecheck_function(function, duplicate_context(Γ))
        except Exception as e:
            g_errors.append(str(e))
        
    ast = ssa_revert(ast)
    return Γ
    


def main():
    parser = argparse.ArgumentParser(description='Program to compile MPIR AST File (JSON) to LaTeX.')

    # Add support for version option
    parser.add_argument('-V', '--version', action='version', version='%(prog)s 1.0')
    parser.add_argument('-i', '--input', metavar='input_file', type=str, nargs='?', help='input file path', default='temp_file.mpirast')
    parser.add_argument('-o', '--output', dest='output_file', metavar='output_file', type=str, help='output file path', default='output.py')
    parser.add_argument('-c', '--config', metavar='config_file', type=str, help='config file path')
    args = parser.parse_args()

    input_file = args.input
    output_file = args.output_file
    config_file = args.config

    # Your code to process input_file and output_file goes here
    ast = parse_json_file(input_file)
    Γ = typecheck_ast(ast)

    if(output_file.endswith(".py")):
        if len(g_errors) == 0:
            build_python(ast, output_file, Γ)
        else:
            with open(output_file, 'w') as file:
                for item in g_errors:
                    file.write("# " + str(item) + '\n')
    elif(output_file.endswith(".tex")):
        if len(g_errors) == 0:
            build_tex(ast, output_file, Γ)
        else:# Open the file for writing
            with open(output_file, 'w') as file:
                # Write each element of the array to the file
                for item in g_errors:
                    file.write("# " + str(item) + '\n')


if __name__ == "__main__":
    main()