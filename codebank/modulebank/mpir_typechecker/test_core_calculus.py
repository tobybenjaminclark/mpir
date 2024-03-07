from typing_context import *
from typing_context import _type, _function_type, _singular_type, _context
from core_calculus import T_Add
from z3 import *
import pytest

def test_t_add():
    σ = z3.Real('σ')
    τ1 = type_create_singular(z3.And(10 <= σ, σ <= 20))
    τ2 = type_create_singular(z3.And(20 <= σ, σ <= 30))
    
    solver = z3.Solver()
    solver.add(T_Add(τ1, τ2)() == z3.And(30 <= σ, 50 >= σ))
    assert solver.check() == sat

test_t_add()