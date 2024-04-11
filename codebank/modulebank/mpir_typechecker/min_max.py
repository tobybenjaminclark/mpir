from z3 import *

# Create a Z3 solver
opt = Optimize()

# Define the variable
x = Int('x')
opt.add(x >= 0)  # Define lower bound
opt.add(x <= 10)  # Define upper bound

def find_min_max(var, opt) -> tuple[int, int]:
    opt.minimize(x)

    # Check if the problem is satisfiable
    if opt.check() == sat:
        # Get the model
        model = opt.model()
        min_val = model.evaluate(x).as_long()
        print("Minimum:", min_val)
    else:
        print("No solution found for minimum.")

    opt = Optimize()

    opt.add(x >= 0)  # Define lower bound
    opt.add(x <= 10)  # Define upper bound
    opt.maximize(x)

    # Check if the problem is satisfiable
    if opt.check() == sat:
        # Get the model
        model = opt.model()
        max_val = model.evaluate(x).as_long()
        print("Maximum:", max_val)
    else:
        print("No solution found for maximum.")

    return min_val, max_val

print(find_min_max(x, opt))
