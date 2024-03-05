
from typing import NamedTuple
from enum import Enum
from z3 import *

# Defining Named Tuples to represent singular types, function types and typing contexts.
type_variants     = Enum('type_variants', ['_function', '_variable'])
_singular_type    = NamedTuple("_singular_type", constraint = z3.Bool)
_function_type    = NamedTuple("_function_type", input_constraints = list[z3.Bool], output_constraint = z3.Bool)
_type             = NamedTuple("_type"         , type = type_variants, logic = _singular_type | _function_type)
_context          = NamedTuple("_context"      , identifier = str, bindings = dict[str: _type])

# Defining a function to show a command line representation of the current typing context.
_context.__repr__ = lambda self: f"Typing Context '{self.identifier}' :\n" + "\n".join([
    f" · {k:<{max(len(k) for k in self.bindings.keys())}} :: {v.logic.constraint}" if isinstance(v.logic, _singular_type) else
    f" · {k:<{max(len(k) for k in self.bindings.keys())}} :: [{', '.join(map(str, v.logic.input_constraints))}] → {v.logic.output_constraint}" for k, v in self.bindings.items()])

# Creates a singular variable type 
def type_create_singular(constraint: z3.Bool) -> _type:
    return _type(type_variants._variable, _singular_type(constraint))

# Creates a function type
def type_create_function(input_constraints: list[z3.Bool], output_constraint: z3.Bool) -> _type:
    return _type(type_variants._function, _function_type(input_constraints, output_constraint))

# Creates a context (binding of identifiers to types)
def context_create(identifier: str = 'Γ') -> _context:
    return _context(identifier, {})

# Binds a type within a typing context to an identifier
def add_type_to_context(context: _context, identifier: str, type_value: _type) -> _context:
    return _context(context.identifier, {**context.bindings, identifier: type_value} if type_value.type in {type_variants._variable, type_variants._function} else None)

# Checks if one type definition has intersection with another type definition.
def is_intersecting(subtype: z3.Bool, basetype: z3.Bool) -> True | False:
    type_solver = z3.Solver()
    type_solver.add(And(subtype, basetype))
    return type_solver.check() == z3.sat

# Check if one type definition is a subtype of another type definition.
def is_subtype(P: z3.Bool, Q: z3.Bool, type_variable: z3.Real = Real('σ')) -> True | False:  
    implication_solver = z3.Solver()
    implication_solver.add(z3.ForAll(type_variable, z3.Implies(P, Q)))
    return implication_solver.check() == z3.sat

# Gets the relation between 2 types. 1: no intersection, 2: intersecting, 3: subtype relation.
def get_relation(P: z3.Bool, Q: z3.Bool, type_variable: z3.Real = Real('σ')) -> 1 | 2 | 3:
    return 3 if(is_subtype(P, Q, type_variable)) else 2 if is_intersecting(P, Q) else 1

# Example usage
def test():
    a = context_create()
    s = z3.Real('s')
    b = type_create_singular(True)
    c = type_create_singular(s > 10)
    d = type_create_function([True, s > 5], s > 10)
    a = add_type_to_context(a, "var", b)
    a = add_type_to_context(a, "var2", c)
    a = add_type_to_context(a, "var2", d)
    print(a)
if __name__ == "__main__": test()