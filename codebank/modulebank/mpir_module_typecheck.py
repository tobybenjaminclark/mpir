import argparse
import json
import os
import z3

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


class TypeCheck():
    def __init__(self, ast:dict) -> None:

        # Validate AST
        if not validate_ast(ast): raise Exception("Invalid AST")
        self.types: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "TYPE_DECLARATION"]
        self.types_logic: dict[str:z3] = {}
        self.functions: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARLATION"]

        self.validate_types()

    def validate_functions(self) -> None:
        pass

    def validate_types(self) -> None:
        
        print("Validating Types")
        for type_index, type in enumerate(self.types):

            # Create Solver for Curernt Type
            type_solver: z3.Solver = z3.Solver()
            self.types_logic[type["IDENTIFIER"]] = form_expression(type_solver, type["LOGIC"])
            type_solver.add(self.types_logic[type["IDENTIFIER"]])

            # Check Solver to make ensure type satisfiability
            if type_solver.check() == z3.sat: print(f"  → Type " + type["IDENTIFIER"] + " is satisfiable")
            else: print(f"  → Type " + type["IDENTIFIER"] + " is unsatisfiable")
                
            continue
        return None




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



def validate_ast(ast) -> bool:
    return True



ast = parse_json_file("testj.json")
a = TypeCheck(ast)