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

# Function to test adding to a Typing Context and fetching using container, `in`.
def test_typing_context_container():
    Γ = context_create()
    Γ = add_type_to_context(Γ, "τ", type_create_singular(True))
    assert "τ" in Γ

# Function to test adding to a Typing Context and fetching using getter.
def test_typing_context_getter():
    Γ = context_create()
    τ = type_create_singular(True)
    Γ = add_type_to_context(Γ, "τ", τ)  
    assert get_type_from_context(Γ, "τ") == τ

# Function to test addition override.
def test_typing_context_addition_override():
    Γ = context_create()
    τ = type_create_singular(True)
    Γ =  Γ + ("τ", τ) 
    assert get_type_from_context(Γ, "τ") == τ

# Execute all defined tests.
if __name__ == "__main__":
    pytest.main()