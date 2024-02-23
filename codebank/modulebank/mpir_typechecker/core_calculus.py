from z3 import *
from typing_context import *
from functools import wraps

Numerical = True

def inject_variables(context):
    def variable_injector(func: Function):
        @wraps(func)
        def decorator(*args, **kwargs):
            func_globals = func.__globals__
            saved_values = {key: func_globals[key] for key in context if key in func_globals}
            func_globals.update(context)
            try: result = func(*args, **kwargs)
            finally: func_globals.update(saved_values) 
            return result
        return decorator
    return variable_injector

base_types = dict(Numerical=True)

@inject_variables(base_types)
def t_add(t1: z3.Bool, t2: z3.Bool) -> True|False:
    return get_relation(t1, Numerical, Real('σ')) and get_relation(t2, Numerical, Real('σ'))
