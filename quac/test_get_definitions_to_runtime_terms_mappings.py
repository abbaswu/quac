"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=get_definitions_to_runtime_terms_mappings test_get_definitions_to_runtime_terms_mappings.py
- Generate an HTML report: coverage html
"""

import ast

from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings


if __name__ == '__main__':
    from test_modules import nested_class_and_nested_async_function

    module = nested_class_and_nested_async_function
    module_name: str = module.__name__

    with open(module.__file__, 'r') as fp:
        code = fp.read()
        module_node = ast.parse(code)

    (
        top_level_class_definitions_to_runtime_classes,
        unwrapped_runtime_functions_to_named_function_definitions
    ) = get_definitions_to_runtime_terms_mappings(
        [module_name],
        [module],
        [module_node]
    )

    top_level_class_definitions_and_runtime_classes_list = list(top_level_class_definitions_to_runtime_classes.items())
    unwrapped_runtime_functions_and_named_function_definitions_list = list(unwrapped_runtime_functions_to_named_function_definitions.items())

    for top_level_class_definition, runtime_class in top_level_class_definitions_and_runtime_classes_list:
        assert top_level_class_definition.name == runtime_class.__name__

    for unwrapped_runtime_function, named_function_definition in unwrapped_runtime_functions_and_named_function_definitions_list:
        assert unwrapped_runtime_function.__name__ == named_function_definition.name

    runtime_classes = set(top_level_class_definitions_to_runtime_classes.values())
    assert {nested_class_and_nested_async_function.Outer, nested_class_and_nested_async_function.OuterClass} == runtime_classes

    runtime_functions = set(unwrapped_runtime_functions_to_named_function_definitions.keys())
    assert {nested_class_and_nested_async_function.fetch_and_process, nested_class_and_nested_async_function.OuterClass.__init__, nested_class_and_nested_async_function.OuterClass.outer_method, nested_class_and_nested_async_function.OuterClass.get_url} == runtime_functions
