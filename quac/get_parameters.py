import ast
import typing

from type_definitions import FunctionDefinition


def get_parameters(function_definition: FunctionDefinition):
    """
    Get the parameters of a function definition.
    """
    arguments: ast.arguments = function_definition.args

    posargs: list[ast.arg] = []
    vararg: typing.Optional[ast.arg] = None
    kwonlyargs: list[ast.arg] = []
    kwarg: typing.Optional[ast.arg] = None

    for arg in arguments.posonlyargs:
        posargs.append(arg)

    for arg in arguments.args:
        posargs.append(arg)

    vararg = arguments.vararg

    for kwonlyarg in arguments.kwonlyargs:
        kwonlyargs.append(kwonlyarg)

    kwarg = arguments.kwarg

    return posargs, vararg, kwonlyargs, kwarg
