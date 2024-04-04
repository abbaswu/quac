import ast

from collections.abc import Generator


def handle_ast_import(ast_import: ast.Import) -> Generator[tuple[str, str], None, None]:
    for ast_alias in ast_import.names:
        module_name = ast_alias.name
        module_name_alias = ast_alias.asname
        if module_name_alias is None:
            module_name_alias = module_name
        yield module_name, module_name_alias
