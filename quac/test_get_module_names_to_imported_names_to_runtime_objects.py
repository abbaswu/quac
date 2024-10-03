"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=get_module_names_to_imported_names_to_runtime_objects test_get_module_names_to_imported_names_to_runtime_objects.py
- Generate an HTML report: coverage html
"""

import importlib


from get_module_names_to_imported_names_to_runtime_objects import get_module_names_to_imported_names_to_runtime_objects
from static_import_analysis import do_static_import_analysis


if __name__ == '__main__':
    module_search_absolute_path = '.'

    (
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict,
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict
    ) = do_static_import_analysis(module_search_absolute_path, 'static_import_analysis')


    # Import modules
    module_name_to_module = {}
    for module_name, file_path in module_name_to_file_path_dict.items():
        module_name_to_module[module_name] = importlib.import_module(module_name)


    d = get_module_names_to_imported_names_to_runtime_objects(
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict,
        module_name_to_module
    )

    import ast
    import logging
    import os
    import typing

    from collections.abc import Generator
    from functools import lru_cache

    import static_import_analysis.get_imports_and_raw_import_froms_in_python_file
    from static_import_analysis.generate_ast_arg import generate_ast_arg
    from static_import_analysis.get_ast_for_python_file import get_ast_for_python_file
    from static_import_analysis.get_functions_and_classes_in_ast_module import get_functions_and_classes_in_ast_module
    from static_import_analysis.get_imports_and_import_froms_in_ast_module import get_imports_and_import_froms_in_ast_module
    from static_import_analysis.get_imports_and_raw_import_froms_in_ast_module import get_imports_and_raw_import_froms_in_ast_module
    from static_import_analysis.get_imports_and_raw_import_froms_in_python_file import get_imports_and_raw_import_froms_in_python_file
    from static_import_analysis.get_module_names_and_file_paths_for_pure_python_project import get_module_names_and_file_paths_for_pure_python_project

    from static_import_analysis.handle_ast_import import handle_ast_import
    from static_import_analysis.handle_ast_import_from import handle_ast_import_from

    GROUND_TRUTH = {
        'static_import_analysis.generate_ast_arg': {'ast': ast, 'Generator': Generator},
        'static_import_analysis.get_ast_for_python_file': {'ast': ast, 'lru_cache': lru_cache},
        'static_import_analysis.get_functions_and_classes_in_ast_module': {'ast': ast, 'generate_ast_arg': generate_ast_arg},
        'static_import_analysis.get_imports_and_import_froms_in_ast_module': {'ast': ast, 'get_imports_and_raw_import_froms_in_ast_module': get_imports_and_raw_import_froms_in_ast_module},
        'static_import_analysis.get_imports_and_import_froms_in_python_file': {k: v for k, v in static_import_analysis.get_imports_and_raw_import_froms_in_python_file.__dict__.items() if not k.startswith('_')},
        'static_import_analysis.get_imports_and_raw_import_froms_in_ast_module': {'ast': ast, 'handle_ast_import': handle_ast_import, 'handle_ast_import_from': handle_ast_import_from},
        'static_import_analysis.get_imports_and_raw_import_froms_in_python_file': {'ast': ast, 'get_ast_for_python_file': get_ast_for_python_file, 'handle_ast_import': handle_ast_import, 'handle_ast_import_from': handle_ast_import_from},
        'static_import_analysis.get_module_names_and_file_paths_for_pure_python_project': {'os': os, 'Generator': typing.Generator},
        'static_import_analysis.handle_ast_import': {'ast': ast, 'Generator': Generator},
        'static_import_analysis.handle_ast_import_from': {'ast': ast, 'Generator': Generator},
        'static_import_analysis': {'ast': ast, 'logging': logging, 'get_module_names_and_file_paths_for_pure_python_project': get_module_names_and_file_paths_for_pure_python_project, 'get_functions_and_classes_in_ast_module': get_functions_and_classes_in_ast_module, 'get_imports_and_import_froms_in_ast_module': get_imports_and_import_froms_in_ast_module},
    }

    assert d == GROUND_TRUTH
