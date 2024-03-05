from typing_context import *
import pytest

# Function to test a singular type definition.
def test_type_singular():
    τ = type_create_singular(True)
    assert τ.logic.constraint == True
    assert τ.type == type_variants._variable

# Function to test a function type definition.
def test_type_function():
    τ = type_create_function([True, True], True)
    assert τ.logic.input_constraints == [True, True]
    assert τ.logic.output_constraint == True
    assert τ.type == type_variants._function

# Function to test adding to a Typing Context.
def test_typing_context():
    Γ = context_create()
    Γ = add_type_to_context(Γ, "τ", type_create_singular(True))
    assert "τ" in Γ

# Execute all defined tests.
if __name__ == "__main__":
    pytest.main()