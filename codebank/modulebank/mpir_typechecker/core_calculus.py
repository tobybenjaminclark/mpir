from z3 import *
from typing_context import *
from functools import wraps

Numerical = True

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

base_types = dict(Numerical=True)

# Function to verify the T-Add Rule (Addition of Types)
@inject_variables(base_types)
def T_Add(τ1: z3.Bool, τ2: z3.Bool) -> True|False:
    return get_relation(τ1, Numerical, Real('σ')) and get_relation(τ2, Numerical, Real('σ'))
