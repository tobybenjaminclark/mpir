from z3 import *
from typing_context import *
from typing_context import _type, _context
from functools import wraps
from bound_check import *

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

base_types = dict(Numerical = type_create_singular(True))



# Function to verify the [T-Add] Rule
@inject_variables(base_types)
def T_Add(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> bool:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint), get_supremum(τ1.logic.constraint)
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint), get_supremum(τ2.logic.constraint)
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound, greatest_upper_bound = τ1_i + τ2_i, τ1_s + τ2_s
    return lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ)



# Function to verify the [T-Mult] Rule
@inject_variables(base_types)
def T_Mult(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> bool:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint), get_supremum(τ1.logic.constraint)
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint), get_supremum(τ2.logic.constraint)
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound, greatest_upper_bound = τ1_i * τ2_i, τ1_s * τ2_s
    return lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ)
        


# Function to verify the [T-Sub] Rule
@inject_variables(base_types)
def T_Sub(τ1: _type, τ2: _type, σ: z3.Real = Real('σ')) -> bool:
    τ1_i, τ1_s = get_infimum(τ1.logic.constraint), get_supremum(τ1.logic.constraint)
    τ2_i, τ2_s = get_infimum(τ2.logic.constraint), get_supremum(τ2.logic.constraint)
    if get_relation(τ1, Numerical, σ) == 1 or get_relation(τ2, Numerical, σ) == 1: return False
    
    # Calculate new infimum and supremum and constrain returned type within that raqnge.
    greatest_lower_bound, greatest_upper_bound = τ1_i - τ2_s, τ1_s - τ2_i
    return lambda: z3.And(greatest_lower_bound <= σ, greatest_upper_bound >= σ)



"""
# Function to verify the T-Subtract Rule [τ1 ≤ {Numerical|P} ^ τ2 ≤ {Numerical|P} → (τ1 - τ2): {Numerical|ε}]
@inject_variables(base_types)
def T_Sub(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False


# Function to verify the T-Multiplication Rule [τ1 ≤ {Numerical|P} ^ τ2 ≤ {Numerical|P} → (τ1 * τ2): {Numerical|ε}]
@inject_variables(base_types)
def T_Multiply(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False


# Function to verify the T-Division Rule [τ1 ≤ {Numerical|P} ^ τ2 ≤ {Numerical|P} ^ τ2 ≮ {Numerical|σ == 0} → (τ1 / τ2): {Numerical|ε}]
@inject_variables(base_types)
def T_Division(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:   
    return False if is_subtype(τ2, ((σ := Real('σ')) == 0)) else (Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False)


# Function to verify the T-FuncCall Rule [f {τ1 ×...× τn ⇝ τ} ^ αi ≤ τi → f α1 → an : τ]
@inject_variables(base_types)
def T_FuncCall(ψ: tuple[list[z3.Bool], z3.Bool], α: z3.Bool) -> Union[bool, z3.Bool]:
    return ψ[1] if len(failures := [True for τn, αn in zip(ψ[0], α) if not is_subtype(αn, τn)]) == 0 else False


# Function to verify the T-FuncCall Rule [f {τ1 ×...× τn ⇝ τ} ^ αi ≤ τi → f α1 → an : τ]
@inject_variables(base_types)
def T_SetCall(σ: z3.Bool, e: z3.Bool) -> Union[bool, z3.Bool]:
    return is_subtype(e, σ)
"""