import ast
import typing
from collections import defaultdict

from get_parameters import get_parameters
from scoped_evaluation_order_node_visitor import NodeProvidingScope, scoped_evaluation_order_node_visitor


def get_function_definitions_to_parameters_name_parameter_mappings_and_return_values(
    module_nodes: typing.Iterable[ast.Module]
):
    function_definitions_to_parameters_name_parameter_mappings_and_return_values: dict[
        ast.AST,
        tuple[typing.Sequence[ast.AST], typing.Mapping[str, ast.AST], ast.AST]
    ] = {}

    def collect_parameter_return_value_information_callback(
            node: ast.AST,
            scope_stack: list[NodeProvidingScope],
    ):
        # ast.FunctionDef(name, args, body, decorator_list, returns, type_comment)
        # ast.AsyncFunctionDef(name, args, body, decorator_list, returns, type_comment)
        # ast.Lambda(args, body)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            # Initialize parameter list.
            (
                posargs,
                vararg,
                kwonlyargs,
                kwarg
            ) = get_parameters(node)

            parameter_name_to_parameter_mapping: dict[str, ast.arg] = {}
            for parameter in posargs + kwonlyargs:
                if parameter.arg not in parameter_name_to_parameter_mapping:
                    parameter_name_to_parameter_mapping[parameter.arg] = parameter
            
            return_value = ast.AST()
            # Let the return value inherit the node's attributes
            if (lineno := getattr(node, 'lineno', None)) is not None:
                setattr(return_value, 'lineno', lineno)

            if (col_offset := getattr(node, 'col_offset', None)) is not None:
                setattr(return_value, 'col_offset', col_offset)
            
            if (end_lineno := getattr(node, 'end_lineno', None)) is not None:
                setattr(return_value, 'end_lineno', end_lineno)
            
            if (end_col_offset := getattr(node, 'end_col_offset', None)) is not None:
                setattr(return_value, 'end_col_offset', end_col_offset)

            function_definitions_to_parameters_name_parameter_mappings_and_return_values[node] = (
                posargs,
                parameter_name_to_parameter_mapping,
                return_value
            )

    for module_node in module_nodes:
        scoped_evaluation_order_node_visitor(module_node, collect_parameter_return_value_information_callback)
    
    return function_definitions_to_parameters_name_parameter_mappings_and_return_values
