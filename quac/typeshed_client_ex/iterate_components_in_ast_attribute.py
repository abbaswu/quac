import ast

from collections.abc import Generator


def iterate_components_in_ast_attribute(ast_attribute: ast.Attribute) -> Generator[str, None, None]:
    value: ast.AST = ast_attribute.value
    attr: str = ast_attribute.attr

    if isinstance(value, ast.Name):
        yield value.id
    elif isinstance(value, ast.Attribute):
        yield from iterate_components_in_ast_attribute(value)
    
    yield attr
