import ast

from .generate_ast_arg import generate_ast_arg


def get_functions_and_classes_in_ast_module(ast_module: ast.Module) -> tuple[
    dict[str, list[str]],
    dict[str, dict[str, list[str]]]
]:
    function_name_to_parameter_name_list_dict: dict[str, list[str]] = dict()
    class_name_to_method_name_to_parameter_name_list_dict: dict[str, dict[str, list[str]]] = dict()

    for node in ast_module.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            function_name: str = node.name
            parameter_name_list: list[str] = [
                ast_arg.arg
                for ast_arg in generate_ast_arg(node)
            ]
            function_name_to_parameter_name_list_dict[function_name] = parameter_name_list
        elif isinstance(node, ast.ClassDef):
            class_name: str = node.name
            method_name_to_parameter_name_list_dict: dict[str, list[str]] = dict()

            for child_node in node.body:
                if isinstance(child_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    method_name: str = child_node.name
                    parameter_name_list: list[str] = [
                        ast_arg.arg
                        for ast_arg in generate_ast_arg(child_node)
                    ]
                    method_name_to_parameter_name_list_dict[method_name] = parameter_name_list

            class_name_to_method_name_to_parameter_name_list_dict[class_name] = method_name_to_parameter_name_list_dict

    return function_name_to_parameter_name_list_dict, class_name_to_method_name_to_parameter_name_list_dict
