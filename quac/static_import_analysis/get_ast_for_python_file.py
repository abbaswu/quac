import ast
from functools import lru_cache


@lru_cache(maxsize=None)
def get_ast_for_python_file(file_path: str) -> ast.Module:
    with open(file_path, 'r') as fp:
        contents = fp.read()
        return ast.parse(contents)
