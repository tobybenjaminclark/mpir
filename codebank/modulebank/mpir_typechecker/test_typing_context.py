from typing_context import *
from typing_context import _type, _function_type, _singular_type, _context
import pytest


# Testing Type Context

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


# Function to test addition override for typing context.
def test_typing_context_addition_override():
    Γ = context_create()
    τ = type_create_singular(True)
    Γ =  Γ + ("τ", τ) 
    assert get_type_from_context(Γ, "τ") == τ


# Function to test removal from typing context.
def test_typing_context_removal():
    Γ = context_create()
    Γ = add_type_to_context(Γ, "τ", type_create_singular(True))
    Γ = remove_type_from_context(Γ, "τ")
    assert get_type_from_context(Γ, "τ") == None


# Function to test removal from typing context.
def test_typing_context_removal_override():
    Γ = context_create()
    Γ = add_type_to_context(Γ, "τ", type_create_singular(True))
    Γ = Γ - "τ"
    assert get_type_from_context(Γ, "τ") == None


# Function to test type hints are correct for typing contexts & types
def test_typing_types():
    τ1 = type_create_singular(True)
    τ2 = type_create_function([True], True)
    Γ = context_create()
    assert type(τ1) == _type and type(τ1.logic) == _singular_type
    assert type(τ2) == _type and type(τ2.logic) == _function_type
    assert type(Γ) == _context






# Testing Type Intersections & Subtypes
    
    
# Function to test the intersect of 2 types
def test_variable_type_intersect():
    σ = Real('σ')
    τ1 = type_create_singular(σ > 10)
    τ2 = type_create_singular(σ > 15)
    τ3 = type_create_singular(σ < 9)
    assert is_intersecting(τ1, τ2) == True
    assert is_intersecting(τ1, τ3) == False


# Function to test the intersect override `/` of 2 types
def test_variable_type_intersect_override():
    σ = Real('σ')
    τ1 = type_create_singular(σ > 10)
    τ2 = type_create_singular(σ > 15)
    τ3 = type_create_singular(σ < 9)
    assert (τ1 & τ2) == True
    assert (τ1 & τ3) == False


# Function to test the subtype relationship between 2 types
def test_variable_type_subtype():
    σ = Real('σ')
    τ1 = type_create_singular(z3.And(σ > 10, σ < 20))
    τ2 = type_create_singular(z3.And(σ > 10, σ < 15))
    assert is_subtype(τ2, τ1) == True
    assert is_subtype(τ1, τ2) == False


# Function to test the subtype relationship override `<` between 2 types
def test_variable_type_subtype_override():
    σ = Real('σ')
    τ1 = type_create_singular(z3.And(σ > 10, σ < 20))
    τ2 = type_create_singular(z3.And(σ > 10, σ < 15))
    assert (τ2 < τ1) == True
    assert (τ1 < τ2) == False
