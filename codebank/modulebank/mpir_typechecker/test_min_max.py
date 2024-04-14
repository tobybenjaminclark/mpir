from min_max import *

# Test find_non_satisfying_values function which finds non satisfying values of a constraint.
def test_find_non_satisfying_values():
    σ = Real('σ')

    # Testing function returns values outside of bounding constraints.
    constr = [σ < 1000, σ > 0]
    values = find_non_satisfying_values(constr, σ)
    for v in values:
        assert float(v) >= 1000 or float(v) <= 0

    # Testing function returns values which do not satisfy refinements of even numbers.
    constr = [ToInt(σ) % 2 == 0]
    values = find_non_satisfying_values(constr, σ)
    for v in values:
        assert float(v) % 2 != 0

# Test find_satisfying_values function which finds satisfying values of a list of constraints.
def test_find_satisfying_values():
    σ = Real('σ')

    # Testing function returns values inside of bounding constraints.
    constr = [σ <= 1000, σ >= 0]
    values = find_satisfying_values(constr, σ)
    for v in values:
        assert float(v) <= 1000 or float(v) >= 0

    # Testing function returns values which satisfy refinements of even numbers.
    constr = [ToInt(σ) % 2 == 0]
    values = find_satisfying_values(constr, σ)
    for v in values:
        assert float(v) % 2 == 0

# Testing find_min_max which finds the minimum and maximum satisfying values of a constraint.
def test_find_min_max():
    
    σ = Real('σ')

    # Set minimum and maximum bounding constraints and ensure these are successfully found.

    min_max = find_min_max([σ <= 1000, σ >= 0], σ)
    assert min_max.min == 0
    assert min_max.max == 1000