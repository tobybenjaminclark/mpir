import argparse
import json
import os
import z3
from mpir_module_context import *
from core_calculus import *

def convert_operator_to_z3(solver, operator: str, left, right):
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

def form_expression(solver, type_logic: dict):

    match type_logic["DATATYPE"]:

        case "OPERATOR":
            left = form_expression(solver, type_logic["LEFT"])
            right = form_expression(solver, type_logic["RIGHT"])
            return convert_operator_to_z3(solver, type_logic["DATA"], left, right)

        case "IDENTIFIER":
            return z3.Real('x')

        case "STRING_LITERAL":
            pass

        case "NUMERICAL_LITERAL":
            return z3.RealVal(type_logic["DATA"])  # Convert to Z3 Real value

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

from z3 import *

def validate_ast(ast) -> bool:
    return True

def get_operator(operator_str):
    operators = {"+": lambda x, y: x + y,
                 "-": lambda x, y: x - y,
                 "*": lambda x, y: x * y,
                 "/": lambda x, y: x / y}

    return operators.get(operator_str, None)

def type_ast_expression(ast, context) -> bool:
    x = Real('σ')
    match ast["TYPE"]:
        case "EXPRESSION_IDENTIFIER":
            print("this: ", context[1][ast["IDENTIFIER"]])
            return lambda: context[1][ast["IDENTIFIER"]]()
        case "EXPRESSION_NUMERICAL_LITERAL":
            return lambda: x == ast["VALUE"]
        case "EXPRESSION_OPERATOR":
            if ast["IDENTIFIER"] == "+":
                l =type_ast_expression(ast["LEFT"], context)
                r = type_ast_expression(ast["RIGHT"], context)
                return T_Add(l(), r())

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
                "VALUE": 1.000000
            },
            "RIGHT" : {
              "TYPE" : "EXPRESSION_IDENTIFIER",
              "IDENTIFIER" : "a"
            }
        }
    }



class TypeCheck():
    def __init__(self, ast:dict) -> None:

        # Validate AST
        if not validate_ast(ast): raise Exception("Invalid AST")
        self.types: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "TYPE_DECLARATION"]
        self.types_logic = context_create()
        self.functions: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]
        self.function_io = [(node["IDENTIFIER"], node["INPUTS"], node["RETURN_TYPE"]) for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]
        for n in self.function_io:
            print(n[0], "::" ,n[1], "->", n[2])

        self.validate_types()
        self.validate_functions()

        global expression_dict
        x = Real('σ')
        context_add(self.types_logic, "a", lambda: z3.And(x > 10, x < 20))
        print(type_ast_expression(expression_dict, self.types_logic)())
        print("\n\n\n")
            

    def validate_functions(self) -> None:
        for function_index, func in enumerate(self.functions):        
            
            # Setup Typing Context for this Function & Populate it with input types
            # context: dict[str:z3] = {arg: self.types_logic[func["INPUTS"][index]] for index, arg in enumerate(func["ARGUMENTS"])}
            context: dict[str:z3] = {}

            for index, statement in enumerate(func["BODY"]):
                if(statement["TYPE"] == "TYPE_ASSIGNMENT"):
                    context[statement["IDENTIFIER"]] = statement["ASSIGNED_TYPE"]
                    print("Type Assignment to " + statement["IDENTIFIER"] + " ( has type: " + str(context[statement["IDENTIFIER"]]) + ")")
                if(statement["TYPE"] == "VALUE_ASSIGNMENT"):
                    print("Value Assignment to " + statement["IDENTIFIER"] + " ( has type: " + str(context[statement["IDENTIFIER"]]) + ")")
                    if(statement["EXPRESSION"]["TYPE"] == "EXPRESSION_NUMERICAL_LITERAL"):
                        print("Literal!")
                continue    
            print(context)
        return None

    def validate_types(self) -> None:
        
        print("Validating Types")
        for type_index, type in enumerate(self.types):

            # Create Solver for Curernt Type
            type_solver: z3.Solver = z3.Solver()
            context_add(self.types_logic, type["IDENTIFIER"], form_expression(type_solver, type["LOGIC"]))
            type_solver.add(context_search(self.types_logic, type["IDENTIFIER"]))

            # Check Solver to make ensure type satisfiability
            if type_solver.check() == z3.sat: print(f"  → Type " + type["IDENTIFIER"] + " is satisfiable ", context_search(self.types_logic, type["IDENTIFIER"]))
            else: print(f"  → Type " + type["IDENTIFIER"] + " is unsatisfiable")
                
            continue
        return None


ast = parse_json_file("testj.json")
a = TypeCheck(ast)