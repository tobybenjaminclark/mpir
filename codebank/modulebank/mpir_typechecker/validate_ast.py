from typing import NamedTuple

_ast = NamedTuple()

def validate_function_declaration(node: dict) -> _ast | None:
    return None

def validate_type_declaration(node: dict) -> _ast | None:
    return None

def validate_ast_node(node: dict) -> _ast | None:
    if    node.get("TYPE", None) == "FUNCTION_DECLARATION": return validate_function_declaration(node)
    elif  node.get("TYPE", None) == "TYPE_DECLARATION": return validate_type_declaration(node)
    else: return None


def validate_ast(ast: dict) -> _ast | None:
    if "CONTENTS" not in ast: return None
    for node in ast: validate_node(node)