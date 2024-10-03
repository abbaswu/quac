import ast

from collections.abc import Generator


def generate_ast_arg(ast_function_def: ast.FunctionDef) -> Generator[
    ast.arg,
    None,
    None
]:
    args: ast.arguments = ast_function_def.args

    yield from args.posonlyargs

    yield from args.args

    if args.vararg is not None:
        yield args.vararg

    yield from args.kwonlyargs

    if args.kwarg is not None:
        yield args.kwarg
