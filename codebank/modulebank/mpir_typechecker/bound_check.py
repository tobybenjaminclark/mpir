import z3
from functools import partial

def _get_combine_func(index: int):
    if index == 1:  return partial(max, default=float('-inf'))
    elif index == 2: return partial(min, default=float('inf'))
        

def get_bound(t, combine_func_index, default_value):
    if z3.is_and(t):
        bounds = [get_bound(arg, 1 if combine_func_index == 2 else 2, default_value) for arg in t.children()]
        return _get_combine_func(combine_func_index)(bounds) 
    elif z3.is_or(t):
        bounds = [get_bound(arg, combine_func_index, default_value) for arg in t.children()]
        return _get_combine_func(combine_func_index)(bounds)        
    elif z3.is_lt(t) or z3.is_gt(t):
        bound_value = z3.simplify(t.children()[1])
        return float(bound_value.as_long()) if z3.is_const(bound_value) else default_value
    else:
        return default_value

def get_infimum(predicate) -> float:
    return get_bound(predicate, 1, float('-inf'))

def get_supremum(predicate) -> float:
    return get_bound(predicate, 2, float('inf'))

# Test expression
x = z3.Real('x')
bool_expression = z3.And(z3.And(x > 5, 10 > x), z3.And(x > 0, 15 > x))
print(bool_expression)

# Calculate and print the infimum
infimum_value = get_infimum(bool_expression)
print(f"The infimum of the expression is: {infimum_value}")

# Calculate and print the supremum
supremum = get_supremum(bool_expression)
print(f"The supremum of the expression is: {supremum}")
