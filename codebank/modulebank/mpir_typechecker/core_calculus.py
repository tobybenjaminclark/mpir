from z3 import *
from typing_context import *
from functools import wraps

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

base_types = dict(Numerical = True)

# Function to verify the T-Add Rule (Addition of Types)
@inject_variables(base_types)
def T_Add(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False

# Function to verify the T-Subtract Rule (Subtraction of Types)
@inject_variables(base_types)
def T_Sub(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False

# Function to verify the T-Multiplication Rule (Subtraction of Types)
@inject_variables(base_types)
def T_Multiply(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False

# Function to verify the T-Division Rule (Division of Types)
@inject_variables(base_types)
def T_Division(τ1: z3.Bool, τ2: z3.Bool) -> Union[bool, z3.Bool]:
    return False if is_subtype(τ2, ((σ := Real('σ')) == 0)) else (Numerical if get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ')) else False)
