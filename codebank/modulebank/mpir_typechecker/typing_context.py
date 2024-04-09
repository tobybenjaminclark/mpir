
from typing import NamedTuple
from enum import Enum
from z3 import *

# Defining Named Tuples to represent singular types, function types and typing contexts.
type_variants  = Enum('type_variants', ['_function', '_variable', '_list'])
_singular_type = NamedTuple("_singular_type", constraint = z3.Bool)
_function_type = NamedTuple("_function_type", input_constraints = list[z3.Bool], output_constraint = z3.Bool)
_list_type     = NamedTuple("_list_type"    , element_type = "_type", length_constraint = z3.Bool, list_constraint = z3.Bool)
_type          = NamedTuple("_type"         , type = type_variants, logic = _singular_type | _function_type | _list_type)
_context       = NamedTuple("_context"      , identifier = str, bindings = dict[str: _type])

# Defining a function to show a command line representation of the current typing context.

_singular_type.__repr__ = lambda self: f"σ | {self.constraint()}"
_function_type.__repr__ = lambda self: f"[{', '.join(str(c()) for c in self.input_constraints)}] -> {self.output_constraint()}"
_list_type.__repr__ = lambda self: f"∀σ | {self.element_type.logic.__repr__()}, P(|L|) = {self.length_constraint()}, θ = {self.list_constraint()}"

_context.__repr__ = lambda self: f"Typing Context '{self.identifier}' :\n" + "\n".join([
        f" · {k:<{max(len(k) for k in self.bindings.keys())}} :: {v.logic.__repr__()}" if isinstance(v.logic, _singular_type) else
        f" · {k:<{max(len(k) for k in self.bindings.keys())}} :: {v.logic.__repr__()}" if isinstance(v.logic, _list_type) else
        f" · {k:<{max(len(k) for k in self.bindings.keys())}} :: {v.logic.__repr__()}" for k, v in self.bindings.items()
        ])

# Override the `in`, `add` and `subtract` methods/operators
_context.__contains__ = lambda self, item: item in self.bindings
_context.__add__ = lambda self, other: add_type_to_context(self, other[0], other[1])
_context.__sub__ = lambda self, other: remove_type_from_context(self, other)

# Type Relationship Bindings for `τ1 < τ2` and `τ1 and τ2`
_type.__lt__ = lambda self, other: is_subtype(self, other)  
_type.__and__ = lambda self, other: is_intersecting(self, other)






# Function to create a singular type instance (τ: B|P).
def type_create_singular(constraint: z3.Bool) -> _type:
    return _type(type_variants._variable, _singular_type(constraint))

# Function to create a function type instance (τ1 x ... x τn → τ0)
def type_create_function(input_constraints: list[z3.Bool], output_constraint: z3.Bool) -> _type:
    return _type(type_variants._function, _function_type(input_constraints, output_constraint))

# Function to create a list type instance (τ0 x ... x τn) ^ P(n) ^ P(τ0 x ... x τn)
def type_create_list(element_constraint: z3.Bool, length_constraint: z3.Bool, list_constraint: z3.Bool) -> _type:
    return _type(type_variants._list, _list_type(element_constraint, length_constraint, list_constraint))

# Creates a context (binding of identifiers to types)
def context_create(identifier: str = 'Γ') -> _context:
    return _context(identifier, {})

# Binds a type within a typing context to an identifier
def add_type_to_context(context: _context, identifier: str, type_value: _type) -> _context:
    if type_value.type in {type_variants._variable, type_variants._function, type_variants._list}:
        new_bindings = {**context.bindings, identifier: type_value}
        return _context(context.identifier, new_bindings)
    else: return _context(context.identifier, context.bindings)
        
# Removes a identifier, type binding from within a typing context.
def remove_type_from_context(context: _context, identifier: str) -> _context:
    return _context(context.identifier, {k: v for k, v in context.bindings.items() if k != identifier})

# Function to get a type from a context, accessed using it's identifier.
def get_type_from_context(context: _context, identifier: str) -> _type|None:
    return context.bindings.get(identifier, None)

# Function to duplicate a typing context (instead of duplicating the reference).
def duplicate_context(original_context: _context) -> _context:
    return _context(original_context.identifier, {k: v for k, v in original_context.bindings.items()})





# Function to check if a singular type intersects with another singular type.
def is_intersecting_singular(subtype: _type, basetype: _type) -> bool | TypeError:
    if subtype.type != basetype.type or subtype.type != type_variants._variable: return TypeError
    type_solver = z3.Solver()
    type_solver.add(And(subtype.logic.constraint, basetype.logic.constraint))
    return type_solver.check() == z3.sat   

# Function to check if a function type intersects with another function type.
def is_intersecting_function(subtype: _type, basetype: _type) -> bool | TypeError:
    if subtype.type != basetype.type or subtype.type != _function_type: return TypeError
    if len(subtype.logic.input_constriants) != len(basetype.logic.input_constriants): return TypeError
    if (output := is_intersecting(subtype.logic.output_constraint, basetype.logic.output_constraint)) == TypeError: return output
    if TypeError in (input_mapping := [is_intersecting(subtype.logic.input_constriants[index], basetype.logic.input_constriants[index]) for index in range(0, len(subtype.logic.input_constraints))]): return filter(lambda v: type(v) == TypeError, input_mapping)
    if len(filter(lambda v: v == True, input_mapping)) == 0 or output == False: return False
    else: return True

# Function to check if a type intersects with another type.
def is_intersecting(subtype: _type, basetype: _type) -> bool | TypeError:
    if subtype.type != basetype.type: return TypeError
    if subtype.type == type_variants._function: return is_intersecting_function(subtype, basetype)
    if subtype.type == type_variants._variable: return is_intersecting_singular(subtype, basetype)





# Function to check if one singular type definition is a subtype of another singular type definition. [T-Sub]
def is_subtype_variable(subtype: _type, basetype: _type, type_variable: z3.Real = Real('σ')) -> bool | TypeError:
    if subtype.type != basetype.type or subtype.type != type_variants._variable: return TypeError
    implication_solver = z3.Solver()
    implication_solver.add(z3.ForAll(type_variable, z3.Implies(subtype.logic.constraint(), basetype.logic.constraint())))
    return implication_solver.check() == z3.sat

# Function to check if one function type definition is a subtype of another function type definition. [T-FuncSub]
def is_subtype_function(subtype: _type, basetype: _type, type_variable: z3.Real = Real('σ')) -> bool | TypeError:
    if len(subtype.logic.input_constriants) != len(basetype.logic.input_constriants): return TypeError
    if (not is_subtype(subtype.logic.output_constraint, basetype.logic.output_constraint)): return False
    inputs = [is_subtype(basetype.logic.input_constriants[index], subtype.logic.input_constriants[index]) for index in range(0, len(subtype.logic.input_constraints))]
    return not (len(filter(lambda v: v == False or v == TypeError, inputs)) > 0)

# Check if one type definition is a subtype of another type definition.
def is_subtype(subtype: _type, basetype: _type, type_variable: z3.Real = Real('σ')) -> True | False:  
    if subtype.type != basetype.type: return TypeError
    if subtype.type == type_variants._function: return is_subtype_function(subtype, basetype, type_variable)
    if subtype.type == type_variants._variable: return is_subtype_variable(subtype, basetype, type_variable)





# Gets the relation between 2 types. 1: no intersection, 2: intersecting, 3: subtype relation.
def get_relation(subtype: _type, basetype: _type, type_variable: z3.Real = Real('σ')) -> 1 | 2 | 3:
    return 3 if(is_subtype(subtype, basetype, type_variable)) else 2 if is_intersecting(subtype, basetype) else 1
