from z3 import *
from typing import NamedTuple
import math
import copy

# Set number of middle values to generate
NUMBER_OF_MIDDLE_VALS = 5

# Create a new base type for the _type_set_repr
_type_set_repr = NamedTuple("_type_set_repr", constraints = list[z3.Bool], min = float, max = float, middle = list[float])

def find_min_max(constr: list[z3.Bool], σ: z3.ArithRef, middle: list[float] = []) -> _type_set_repr:

    # Make a new _type_set_repr class.
    _type_set_repr_duplicate = copy.deepcopy(_type_set_repr)

    # Define some functions to get minimum and maximum of a constraint.
    get_opt = lambda opt, c=constr: (lambda opt, c=constr: opt if opt.add(c) else opt)(Optimize())
    get_min_opt = lambda _σ = σ, c = constr: (lambda opt: opt if opt.minimize(_σ) else opt)(get_opt(c))
    get_max_opt = lambda _σ = σ, c = constr: (lambda opt: opt if opt.maximize(_σ) else opt)(get_opt(c))

    # Get the Minimum Value (0 if there isn't one.)
    if (opt := get_min_opt()).check() == sat: σ_min = opt.model().evaluate(σ).as_decimal(3)
    else: print("No solution found for minimum.")

    # Get the Maximum Value (0 if there isn't one.)
    if (opt := get_max_opt()).check() == sat: σ_max = opt.model().evaluate(σ).as_decimal(3)
    else: print("No solution found for maximum.")
    
    # Generate N middle values.
    σ_max_num, σ_min_num = σ_max, σ_min
    σ_max, σ_min = RealVal(σ_max), RealVal(σ_min)
    z, y, m, middle = Real('z'), Real('y'), [], []
    constr.extend([y == (σ_max + σ_min)/2, (z == If(σ > y, σ - y, y - σ))])
    opt = get_opt(Optimize())
    for i in range(NUMBER_OF_MIDDLE_VALS):
        if opt.check() != sat: break
        mid_val = opt.model()[σ].as_decimal(3)
        middle.append(mid_val)
        m.append(RealVal(mid_val))
        opt.add(σ != m[i])

    # Checking Maxval and Minval (In case an explicit bound is undefined.)
    if (opt := get_opt(Optimize(), constr.extend([σ < σ_min]))).check() == sat:
        σ_min = "-\infty" if float(opt.model().evaluate(σ).as_decimal(3)) < float(σ_min_num) else float(σ_min_num)
    if (opt := get_opt(Optimize(), constr.extend([σ > σ_max]))).check() == sat:
        σ_max = "\infty" if float(opt.model().evaluate(σ).as_decimal(3)) > float(σ_max_num) else float(σ_max_num)

    # Create Type Set Representation
    if len(middle) >= NUMBER_OF_MIDDLE_VALS: show_function = lambda self: "$$\\sigma \\in \\{" + f" {self.min} ... {', '.join(str(self.middle[i]) for i in range(len(self.middle)))} ... {self.max} " + "\\}$$"
    else: show_function = lambda self: "$$\\sigma \\in \\{ " + (' | '.join(str(self.middle[i]) for i in range(len(self.middle)))) + " \\}$$"

    # Form and return _type_set_repr object
    type_set = _type_set_repr_duplicate(constr, σ_min, σ_max, middle)
    _type_set_repr_duplicate.__repr__, _type_set_repr_duplicate.__str__ = show_function, show_function
    return type_set

if __name__ == "__main__":
    x = Real('x')
    a = find_min_max([x > 5, x < 10], x)
    print("Type of x is " + str(a))

