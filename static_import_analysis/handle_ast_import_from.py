import ast

from collections.abc import Generator


def handle_ast_import_from(ast_import_from: ast.ImportFrom) -> Generator[tuple[str, int, str, str], None, None]:
    module_name = ast_import_from.module
    module_level = ast_import_from.level
    for ast_alias in ast_import_from.names:
        imported_name = ast_alias.name
        imported_name_alias = ast_alias.asname
        if imported_name_alias is None:
            imported_name_alias = imported_name
        yield module_name, module_level, imported_name, imported_name_alias
