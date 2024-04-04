import ast
import logging

from .get_module_names_and_file_paths_for_pure_python_project import \
    get_module_names_and_file_paths_for_pure_python_project
from .get_functions_and_classes_in_ast_module import get_functions_and_classes_in_ast_module
from .get_imports_and_import_froms_in_ast_module import get_imports_and_import_froms_in_ast_module


# Returns:
# module_name_to_file_path_dict: dict[str, str]
# module_name_to_function_name_to_parameter_name_list_dict: dict[str, dict[str, list[str]]]
# module_name_to_class_name_to_method_name_to_parameter_name_list_dict: dict[str, dict[str, dict[str, list[str]]]]
# module_name_to_import_tuple_set_dict: dict[str, set[tuple[str, str]]]
# module_name_to_import_from_tuple_set_dict: dict[str, set[tuple[str, str, str]]]
def do_static_import_analysis(
    path_of_directory_containing_project: str,
    module_prefix: str = ''
) -> tuple[
    dict[str, str],
    dict[str, dict[str, list[str]]],
    dict[str, dict[str, dict[str, list[str]]]],
    dict[str, set[tuple[str, str]]],
    dict[str, set[tuple[str, str, str]]]
]:
    module_name_to_file_path_dict: dict[str, str] = {
        module_name: file_path
        for module_name, file_path in get_module_names_and_file_paths_for_pure_python_project(
            path_of_directory_containing_project
        )
        if module_name.startswith(module_prefix)
    }

    invalid_module_name_set: set[str] = set()

    module_name_to_function_name_to_parameter_name_list_dict: dict[str, dict[str, list[str]]] = dict()
    module_name_to_class_name_to_method_name_to_parameter_name_list_dict: dict[str, dict[str, dict[str, list[str]]]] = dict()
    module_name_to_import_tuple_set_dict: dict[str, set[tuple[str, str]]] = dict()
    module_name_to_import_from_tuple_set_dict: dict[str, set[tuple[str, str, str]]] = dict()

    for module_name, file_path in module_name_to_file_path_dict.items():
        with open(file_path, 'r') as fp:
            try:
                contents: str = fp.read()
                ast_module: ast.Module = ast.parse(contents, file_path)
            except Exception:
                logging.exception('Failed to parse module `%s`', module_name)
                invalid_module_name_set.add(module_name)
                continue

            (
                function_name_to_parameter_name_list_dict,
                class_name_to_method_name_to_parameter_name_list_dict
            ) = get_functions_and_classes_in_ast_module(ast_module)

            module_name_to_function_name_to_parameter_name_list_dict[module_name] = function_name_to_parameter_name_list_dict
            module_name_to_class_name_to_method_name_to_parameter_name_list_dict[module_name] = class_name_to_method_name_to_parameter_name_list_dict

            is_package = file_path.endswith('__init__.py')
            import_tuple_set, import_from_tuple_set = get_imports_and_import_froms_in_ast_module(
                ast_module,
                module_name,
                is_package
            )

            module_name_to_import_tuple_set_dict[module_name] = import_tuple_set
            module_name_to_import_from_tuple_set_dict[module_name] = import_from_tuple_set

    # Ensure consistency of module names across all dicts
    for module_name in invalid_module_name_set:
        del module_name_to_file_path_dict[module_name]
    
    return (
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict,
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict
    )
