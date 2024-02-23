from z3 import *
from typing import NewType, Union

# Type Definition for Typing Context as list[str, dict[str: z3.Bool]].
typing_context = NewType('typing_context', tuple[str, dict[str: z3.Bool]])

# Creates a new typing context.
def context_create(name: str = "Γ") -> typing_context:
    return (name ,{})

# Adds a new variable: type binding to an existing context.
def context_add(context: typing_context, identifier: str, refinement: z3.Bool) -> 0|1:
    try: context[1][identifier] = refinement; return 0
    except Exception as e: print(f"Error {e}"); return 1

# Searches a singular context for an identifiers type.
def context_search_individual(context: typing_context, identifier: str) -> Union[z3.Bool, None]:
    return context[1][identifier] if identifier in context[1] else None

# Searches multiple typing contexts for an identifiers type.
def context_search_multiple(contexts: list[typing_context], identifier: str) -> Union[z3.Bool, None]:
    return next((context_search_individual(context, identifier) for context in contexts), None)

# Overload that can search either multiple contexts, or a singular context dependent on argument type.
def context_search(contexts: list[typing_context]|typing_context, identifier: str) -> Union[z3.Bool, None]:
    return context_search_multiple([contexts] if type(contexts[0]) == str else contexts, identifier)

# Checks if one type definition has intersection with another type definition.
def is_intersecting(subtype: z3.Bool, basetype: z3.Bool) -> True | False:
    type_solver = z3.Solver()
    type_solver.add(And(subtype, basetype))
    return type_solver.check() == z3.sat

# Check if one type definition is a subtype of another type definition.
def is_subtype(subtype: z3.Bool, basetype: z3.Bool, type_variable: z3.Real = Real('σ')) -> True | False:  
    implication_solver = z3.Solver()
    implication_solver.add(z3.ForAll(type_variable, z3.Implies(subtype, basetype)))
    return implication_solver.check() == z3.sat

# Gets the relation between 2 types. 1 means no intersection, 2 means intersecting, 3 means subtype relation.
def get_relation(subtype: z3.Bool, basetype: z3.Bool, type_variable: z3.Real = Real('σ')) -> 1|2|3:
    return 3 if(is_subtype(subtype, basetype, type_variable)) else 2 if is_intersecting(subtype, basetype) else 1