import ast

from generate_ast_arg import generate_ast_arg


def get_parameter_name_list_from_ast_function_def(ast_function_def: ast.FunctionDef) -> list[str]:
    return [ ast_arg.arg for ast_arg in generate_ast_arg(ast_function_def) ]
