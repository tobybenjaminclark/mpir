from z3 import *
import math

# Create a Z3 solver
NUMBER_OF_MIDDLE_VALS = 5

# Define the variable
x = Real('x')
constraints = []
constraints.append(x >= 0)  # Define lower bound
constraints.append(ToInt(x) == x)
constraints.append(ToInt(x) % 2 == 0)

def find_min_max(constraints, σ, middle = []) -> tuple[int, int, int]:
    
    # Define some functions to get minimum and maximum of a constraint.
    get_opt = lambda opt, c= constraints: (lambda opt, c=constraints: opt if opt.add(c) else opt)(Optimize())
    get_min_opt = lambda _σ = σ, c = constraints: (lambda opt: opt if opt.minimize(_σ) else opt)(get_opt(c))
    get_max_opt = lambda _σ = σ, c = constraints: (lambda opt: opt if opt.maximize(_σ) else opt)(get_opt(c))

    # Get the Minimum Value (0 if there isn't one.)
    if (opt := get_min_opt()).check() == sat: σ_min = opt.model().evaluate(σ).as_long()
    else: print("No solution found for minimum.")

    # Get the Maximum Value (0 if there isn't one.)
    if (opt := get_max_opt()).check() == sat: σ_max = opt.model().evaluate(σ).as_long()
    else: print("No solution found for maximum.")
    
    # Generate N middle values.
    opt = get_min_opt(z := Real('z'), constraints.extend([(y := Real('y')) == ((σ_max + σ_min)/2),(z == z3.If(σ > y, σ - y, y - σ))]))
    for _ in range(0, NUMBER_OF_MIDDLE_VALS):
        if opt.check() != sat: raise Exception()
        middle.append(max_val := opt.model().evaluate(σ).as_decimal(3))
        opt.add(σ != max_val)

    # Normalizing Maxval & Minval to medium values
    σ_max = math.inf if all(float(z) <= σ_max for z in middle) else σ_max
    σ_min = math.inf if all(float(z) >= σ_min for z in middle) else σ_min

    return σ_min, middle, σ_max

a, b, c = find_min_max(constraints, x)
print("type of x is {" + f" {a} ... {', '.join(str(b[i]) for i in range(len(b)))}, ... {c} " + "}")

