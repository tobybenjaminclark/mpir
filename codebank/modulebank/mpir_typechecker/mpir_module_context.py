from z3 import *

def validate_ast(ast) -> bool:
    return True

class TypeCheck():
    def __init__(self, ast:dict) -> None:

        # Validate AST
        if not validate_ast(ast): raise Exception("Invalid AST")
        self.types: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "TYPE_DECLARATION"]
        self.types_logic: dict[str:z3] = {}
        self.functions: list[dict] = [node for node in ast["CONTENTS"] if node["TYPE"] == "FUNCTION_DECLARATION"]

        self.validate_types()
        self.validate_functions()

    def validate_functions(self) -> None:
        for function_index, func in enumerate(self.functions):        
            
            # Setup Typing Context for this Function & Populate it with input types
            # context: dict[str:z3] = {arg: self.types_logic[func["INPUTS"][index]] for index, arg in enumerate(func["ARGUMENTS"])}
            context: dict[str:z3] = {}

            for index, statement in enumerate(func["BODY"]):
                if(statement["TYPE"] == "TYPE_ASSIGNMENT"):
                    context[statement["IDENTIFIER"]] = statement["ASSIGNED_TYPE"]
                if(statement["TYPE"] == "VALUE_ASSIGNMENT"):
                    print("Assignment to " + statement["IDENTIFIER"] + " ( has type: " + str(context[statement["IDENTIFIER"]]) + ")")
                continue    
            print(context)
        return None

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