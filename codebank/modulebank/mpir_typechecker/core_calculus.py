from z3 import *
from typing_context import *
from typing_context import _type, _context
from functools import wraps
from bound_check import *

# Decorator Factory to inject base types into core calculus
def inject_variables(context: dict[str, any]) -> callable:
    def variable_injector(func: callable) -> callable:
        @wraps(func)
        def decorator(*args: any, **kwargs: any) -> any:
            func_globals: dict[str, any] = func.__globals__
            saved_values: dict[str, any] = {key: func_globals[key] for key in context if key in func_globals}
            func_globals.update(context)
            try: result: any = func(*args, **kwargs)
            finally: func_globals.update(saved_values)
            return result
        return decorator
    return variable_injector

base_types = dict(Numerical = type_create_singular(lambda: True))



# [T-Add] :: Validates & Infers Refinement of the Addition of 2 types.
@inject_variables(base_types)
def T_Add(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> _type:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint()), get_supremum(τ1.logic.constraint())
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint()), get_supremum(τ2.logic.constraint())
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound, greatest_upper_bound = τ1_i + τ2_i, τ1_s + τ2_s
    return type_create_singular(lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ))



# [T-Mult] :: Validates & Infers Refinement of the Product of 2 types.
@inject_variables(base_types)
def T_Mult(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> _type:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint()), get_supremum(τ1.logic.constraint())
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint()), get_supremum(τ2.logic.constraint())
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound = min(τ1_i * τ2_i, τ1_i * τ2_s, τ1_s * τ2_i, τ1_s * τ2_s)
    greatest_upper_bound = max(τ1_i * τ2_i, τ1_i * τ2_s, τ1_s * τ2_i, τ1_s * τ2_s)
    return type_create_singular(lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ))
        


# [T-Sub] :: Validates & Infers Refinement of the Subtraction of 2 types.
@inject_variables(base_types)
def T_Sub(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> _type:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint()), get_supremum(τ1.logic.constraint())
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint()), get_supremum(τ2.logic.constraint())
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound, greatest_upper_bound = τ1_i - τ2_s, τ1_s - τ2_i
    return type_create_singular(lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ))



# [T-Div] :: Validates & Infers Refinement of the Division of 2 types.
@inject_variables(base_types)
def T_Div(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> _type:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint()), get_supremum(τ1.logic.constraint())
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint()), get_supremum(τ2.logic.constraint())
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound = min(τ1_i / τ2_i, τ1_i / τ2_s, τ1_s / τ2_i, τ1_s / τ2_s)
    greatest_upper_bound = max(τ1_i / τ2_i, τ1_i / τ2_s, τ1_s / τ2_i, τ1_s / τ2_s)
    return type_create_singular(lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ))



# TODO: Add some interval arithmetic
# [T-Comp] :: Validates & Infers Refinement of the Division of 2 types.
@inject_variables(base_types)
def T_Comp(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> _type:
    return type_create_singular(lambda: True)



# [T-FuncCall] :: Validates a Function Call and provides a return type.
@inject_variables(base_types)
def T_FuncCall(inputs: list[_type], function: _type, σ: z3.Real = Real('σ')) -> z3.Bool:
    if function.type != type_variants._function: raise Exception("[T-FuncCall] :: Function is not of base-type Function.")
    input_validation = [inputs[index] < (type_create_singular(function.logic.input_constraints[index])) for index in range(0, len(inputs))]

    if False in input_validation:
        raise Exception("Passed non-subtype arg. ", input_validation)
    else:
        return type_create_singular(function.logic.output_constraint)