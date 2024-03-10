import z3
from functools import partial

# Higher-Order Function that returns a min\max application dependent on the passed index.
def _get_combine_func(index: int) -> partial:
    if index == 2:  return partial(max, default=float(-2147483647))
    elif index == 1: return partial(min, default=float(2147483647))
        
# Function to get the GLB/GUB of a given predicate, dependent on `combine_func_index`
def get_bound(t: z3.Bool, combine_func_index: int, default_value: float) -> float:
    if z3.is_and(t):
        bounds = [get_bound(arg, 1 if combine_func_index == 2 else 2, default_value) for arg in t.children()]
        return _get_combine_func(combine_func_index)(bounds)
    elif z3.is_or(t):
        bounds = [get_bound(arg, combine_func_index, default_value) for arg in t.children()]
        return _get_combine_func(combine_func_index)(bounds)
    elif z3.is_lt(t) or z3.is_gt(t) or z3.is_ge(t) or z3.is_le(t):
        bound_value_0 = z3.simplify(t.children()[0])
        bound_value_1 = z3.simplify(t.children()[1])
        try: float(bound_value_0.as_long()) 
        except: pass
        try: return float(bound_value_1.as_long()) 
        except: pass
        return default_value
    
    elif z3.is_eq(t):
        bound_value_0 = z3.simplify(t.children()[0])
        bound_value_1 = z3.simplify(t.children()[1])
        try: float(bound_value_0.as_long()) 
        except: pass
        try: return float(bound_value_1.as_long()) 
        except: pass
        return default_value
    else:
        return default_value

def get_infimum(predicate) -> float: 
    return get_bound(predicate, 1, float(-2147483647))
def get_supremum(predicate) -> float: 
    return get_bound(predicate, 2, float(2147483647))

if __name__ == "__main__":
    # Test expression
    σ = z3.Real('σ')
    # bool_expression = z3.And(z3.And(x > 5, 10 > 2), z3.And(x > 0, 15 > x))

    bool_expression = lambda: z3.And(10 <= σ, σ <= 20)

    print(bool_expression, ":", bool_expression())
    # Calculate and print the infimum
    infimum_value = get_infimum(bool_expression())
    print(f"The infimum of the expression is: {infimum_value}")

    # Calculate and print the supremum
    supremum = get_supremum(bool_expression())
    print(f"The supremum of the expression is: {supremum}")