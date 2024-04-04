"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=get_attribute_access_result test_get_attribute_access_result.py
- Generate an HTML report: coverage html
"""

import ast
import re

from get_attribute_access_result import get_attribute_access_result
from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings
from type_definitions import *


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

    assert get_attribute_access_result(
        nested_class_and_nested_async_function,
        're',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == re

    assert get_attribute_access_result(
        nested_class_and_nested_async_function,
        'Outer',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == nested_class_and_nested_async_function.Outer

    assert get_attribute_access_result(
        nested_class_and_nested_async_function,
        'fetch_and_process',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == unwrapped_runtime_functions_to_named_function_definitions[nested_class_and_nested_async_function.fetch_and_process]

    assert get_attribute_access_result(
        nested_class_and_nested_async_function.OuterClass,
        'outer_class_var',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == Instance(str)

    assert get_attribute_access_result(
        nested_class_and_nested_async_function.OuterClass,
        '__init__',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == UnboundMethod(nested_class_and_nested_async_function.OuterClass, unwrapped_runtime_functions_to_named_function_definitions[nested_class_and_nested_async_function.OuterClass.__init__])

    o = get_attribute_access_result(
        nested_class_and_nested_async_function,
        'o',
        unwrapped_runtime_functions_to_named_function_definitions
    )

    assert get_attribute_access_result(
        o,
        'get_url',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == UnboundMethod(nested_class_and_nested_async_function.OuterClass, unwrapped_runtime_functions_to_named_function_definitions[nested_class_and_nested_async_function.OuterClass.get_url])

    assert get_attribute_access_result(
        o,
        'outer_method',
        unwrapped_runtime_functions_to_named_function_definitions
    ) == BoundMethod(Instance(nested_class_and_nested_async_function.OuterClass), unwrapped_runtime_functions_to_named_function_definitions[nested_class_and_nested_async_function.OuterClass.outer_method])
