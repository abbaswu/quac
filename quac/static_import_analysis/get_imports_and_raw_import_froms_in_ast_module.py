import ast

from .handle_ast_import import handle_ast_import
from .handle_ast_import_from import handle_ast_import_from


# Returns a `tuple[set[tuple[str, str]], set[tuple[str, int, str, str]]]`
# The first `set[tuple[str, str]]` contains `Import`'s represented as 2-tuples: (module_name, module_name_alias)
# The second `set[tuple[str | None, int, str, str]]]` contains `ImportFrom`'s represented as 4-tuples: (raw_module_name, module_level, imported_name, imported_name_alias)
# References: 
# https://docs.python.org/3/library/ast.html#ast.ClassDef
def get_imports_and_raw_import_froms_in_ast_module(ast_module: ast.Module) -> tuple[set[tuple[str, str]], set[tuple[str | None, int, str, str]]]:
    imports: set[tuple[str, str]] = set()
    raw_import_froms: set[tuple[str, int, str, str]] = set()

    for node in ast.walk(ast_module):
        if isinstance(node, ast.Import):
            for (module_name, module_name_alias) in handle_ast_import(node):
                imports.add((module_name, module_name_alias))
        elif isinstance(node, ast.ImportFrom):
            for (raw_module_name, module_level, imported_name, imported_name_alias) in handle_ast_import_from(node):
                raw_import_froms.add((raw_module_name, module_level, imported_name, imported_name_alias))

    return imports, raw_import_froms
