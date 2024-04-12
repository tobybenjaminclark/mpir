from z3 import *
from typing import NamedTuple
import math
import copy

# Set number of middle values to generate
NUMBER_OF_MIDDLE_VALS = 5
NUMBER_OF_SATISFYING_VALS = 3       

# Create a new base type for the _type_set_repr
_type_set_repr = NamedTuple("_type_set_repr", constraints = list[z3.Bool], min = float, max = float, middle = list[float])

# Gives non satisfying values of a constraint.
def find_non_satisfying_values(constr: list[z3.Bool], σ: z3.ArithRef) -> list[float]:
    """
    Finds values that do not satisfy the constraints.

    Parameters:
        constr (list[z3.Bool]): List of Z3 constraints.
        σ (z3.ArithRef): Z3 arithmetic expression.

    Returns:
        list[float]: List of values that do not satisfy the constraints.
    """

    get_opt = lambda c=constr: (lambda opt, c=c: opt if opt.add(z3.Implies(z3.And(c), False)) else opt)(z3.Solver())
    values_of_σ, z3_values_of_σ, solver = [], [], get_opt()
    
    # Constraint to find values of y, that do not satisfy x
    y, z = Real('y'), Real('z')
    solver.add([z3.ForAll(σ, z3.Exists(y, y != σ)), z == y])

    for i in range(0, NUMBER_OF_SATISFYING_VALS):
        if solver.check() != sat: break
        satisfying_value = float(solver.model().evaluate(σ).as_decimal(3).replace("?", ""))
        z3_values_of_σ.append(z3.RealVal(satisfying_value))
        values_of_σ.append(satisfying_value)
        solver.add(σ != z3_values_of_σ[-1])
    return values_of_σ

# Gives satisfying values of a constraint.
def find_satisfying_values(constr: list[z3.Bool], σ: z3.ArithRef) -> list[float]:
    """
    Finds satisfying values of a constraint.
    
    Parameters:
        constr (list[z3.Bool]): List of Z3 constraints.
        σ (z3.ArithRef): Z3 arithmetic expression.
    
    Returns:
        list[float]: List of satisfying values.
    """
    get_opt = lambda c=constr: (lambda opt, c=constr: opt if opt.add(c) else opt)(Optimize())

    values_of_σ, z3_values_of_σ, opt = [], [], get_opt()
    for i in range(NUMBER_OF_SATISFYING_VALS):
        if opt.check() != sat: break
        z3_values_of_σ.append(RealVal(current_val := opt.model().evaluate(σ).as_decimal(3)))
        values_of_σ.append(current_val)
        opt.add(σ != z3_values_of_σ[i])
    return values_of_σ

def find_min_max(constr: list[z3.Bool], σ: z3.ArithRef, middle: list[float] = []) -> _type_set_repr:
    """
    Finds the minimum and maximum satisfying values of a constraint, find multiple middle satisfying values.
    
    Parameters:
        constr (list[z3.Bool]): List of Z3 constraints.
        σ (z3.ArithRef): Z3 arithmetic expression.
        middle (list[float], optional): List of middle values. Defaults to [].
    
    Returns:
        _type_set_repr: NamedTuple containing constraints, min, max, and middle values.
    """

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
    a = find_min_max([x < 1000, x > 0], x)
    print("Type of x is " + str(a))
    
    a = find_satisfying_values([x < 1000, x > 0], x)
    print("Satisfying values of x include: ", a)

    a = find_non_satisfying_values([x < 1000, x > 0], x)
    print("Non-Satisfying values of x include: ", a)

