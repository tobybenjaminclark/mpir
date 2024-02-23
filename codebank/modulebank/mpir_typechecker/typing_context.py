from z3 import *
from typing import NewType, Union


typing_context = NewType('typing_context', list[str, dict[str: z3.Bool]])

# Creates a new typing context
def context_create(name: str = "Γ") -> typing_context:
    return [name ,{}]

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
    return context_search_multiple([contexts] if type(contexts) == context else contexts, identifier)

def test() -> None:
    a = context_create("test")
    b = context_create("test2")
    context_add(a, "identifier", "aaa")
    print(context_search_multiple([a, b], "identifier"))