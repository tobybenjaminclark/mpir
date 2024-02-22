import argparse
import json
import os
import z3

def convert_operator_to_z3(solver, operator: str, left, right):
    print(operator, left, right)
    operator_mapping = {
        ">": lambda: left > right,
        ">=": lambda: left >= right,
        "<": lambda: left < right,
        "<=": lambda: left <= right,
        "=": lambda: left == right,
        "∧": lambda:z3.And(left, right),
        "∨": lambda: z3.Or(left, right),
        "¬": lambda: z3.Not(left),
        "∀": lambda: z3.ForAll(left, right),
        "∃": lambda: z3.Exists(left, right),
    }

    if operator in operator_mapping:
        return operator_mapping[operator]()
    else:
        # Handle the case where the operator is not recognized
        raise ValueError(f"Unsupported operator: {operator}")

def form_expression(solver, type_logic: dict):
    if type_logic["DATATYPE"] == "OPERATOR":
        left = form_expression(solver, type_logic["LEFT"])
        right = form_expression(solver, type_logic["RIGHT"])
        return convert_operator_to_z3(solver, type_logic["DATA"], left, right)
    elif type_logic["DATATYPE"] == "IDENTIFIER":
        return z3.Real('x')  # Example: You might want to replace this with the actual variable name
    elif type_logic["DATATYPE"] == "STRING_LITERAL":
        pass  # Handle string literals if needed
    elif type_logic["DATATYPE"] == "NUMERICAL_LITERAL":
        return z3.RealVal(type_logic["DATA"])  # Convert to Z3 Real value
    

class TypeCheck():
    def __init__(self, ast:dict) -> None:

        # Validate AST
        if not validate_ast(ast): raise Exception("Invalid AST")
        self.types: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "TYPE_DECLARATION"]
        self.functions: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARLATION"]

        self.check_types()
    
    def check_types(self) -> None:

        for type in self.types:
            s = z3.Solver()
            a = form_expression(s, type["LOGIC"])
            s.add(a)
               
            
            if s.check() == z3.sat:
                model = s.model()
                print(f"Model: {model}")
            else:
                print("Unsatisfiable")

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