from z3 import *
from typing import NewType, Union

# Typing Context Type is list[str, dict[str: z3.Bool]]
typing_context = NewType('typing_context', tuple[str, dict[str: z3.Bool]])

# Creates a new typing context
def context_create(name: str = "Γ") -> typing_context:
    return (name ,{})

# Adds a new variable: type binding to an existing context
def context_add(context: typing_context, identifier: str, refinement: z3.Bool) -> 0|1:
    try: context[1][identifier] = refinement; return 0
    except Exception as e: print(f"Error {e}"); return 1

# Searches a singular context for an identifiers type
def context_search_individual(context: typing_context, identifier: str) -> Union[z3.Bool, None]:
    return context[1][identifier] if identifier in context[1] else None

# Searches multiple typing contexts for an identifiers type
def context_search_multiple(contexts: list[typing_context], identifier: str) -> Union[z3.Bool, None]:
    return next((context_search_individual(context, identifier) for context in contexts), None)

# Overload that can search either multiple contexts, or a singular context dependent on argument type
def context_search(contexts: list[typing_context]|typing_context, identifier: str) -> Union[z3.Bool, None]:
    return context_search_multiple([contexts] if type(contexts[0]) == str else contexts, identifier)






def is_exact_subtype(subtype: z3.Bool, basetype: z3.Bool):
    x = z3.Real('x')  # Use the same variable in both predicates
    implication_solver = z3.Solver()
    implication_solver.add(z3.ForAll(x, z3.Implies(subtype, basetype)))
    return implication_solver.check() == z3.sat

x = z3.Real('x')

# Example 1: 5 < x < 10 is an exact subtype of 0 < x < 20
print("a", is_exact_subtype(
    z3.And(x > 5, x < 10),
    z3.And(x > 0, x < 20)
))  # Output: True

# Example 2: 5 < x < 10 is not an exact subtype of 0 < x < 15
print("b", is_exact_subtype(
    z3.And(x > 0, x < 20),
    z3.And(x > 5, x < 10)
))  # Output: False




def is_subtype(subtype: z3.Bool, basetype: z3.Bool) -> True|False:
    type_solver = z3.Solver()
    type_solver.add(And(subtype, basetype))
    return True if type_solver.check() == z3.sat else False

x = z3.Real('x')
print(is_subtype(
    z3.And(x > 15, x < 25),
    z3.And(x > 10, x < 20)
))




