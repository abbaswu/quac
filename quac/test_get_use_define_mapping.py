"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=get_use_define_mapping test_get_use_define_mapping.py
- Generate an HTML report: coverage html
"""

import ast
import collections
import builtins

from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings
from get_use_define_mapping import get_use_define_mapping
from type_definitions import *
from unwrap import unwrap


if __name__ == '__main__':
    from test_modules import function_class_definition_and_imports

    module = function_class_definition_and_imports
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

    names_to_dummy_definition_nodes = {}

    for key, value in __builtins__.__dict__.items():
        name = key
        unwrapped_value = unwrap(value)
        if isinstance(unwrapped_value, (RuntimeClass, UnwrappedRuntimeFunction)):
            dummy_definition_node = ast.AST()
            setattr(dummy_definition_node, 'lineno', name)
            names_to_dummy_definition_nodes[name] = dummy_definition_node

    for value in (True, False, Ellipsis, None, NotImplemented):
        name = str(value)
        dummy_definition_node = ast.AST()
        setattr(dummy_definition_node, 'lineno', name)
        names_to_dummy_definition_nodes[name] = dummy_definition_node

    # How to handle global functions?

    define_to_uses = dict(get_use_define_mapping(module_node, names_to_dummy_definition_nodes).itersets())

    def transform_node(node: ast.AST):
        return (
            getattr(type(node), '__name__', ''),
            getattr(node, 'lineno', -1)
        )

    transformed_define_to_uses = {
        transform_node(k): collections.Counter(
            transform_node(i) for i in v
        )
        for k, v in define_to_uses.items()
    }

    GROUND_TRUTH_TRANSFORMED_DEFINE_TO_USES = {
        # shell_sort
        ('FunctionDef', 1): {('FunctionDef', 1): 1, ('Name', 19): 1},
        # xs
        ('Name', 2): {('Name', 2): 1, ('Name', 3): 1},
        # x
        ('Name', 3): {
            ('Name', 8): 2,
            ('Name', 9): 1,
            ('Name', 3): 1,
            ('Name', 4): 1,
            ('Name', 10): 1
        },
        # i
        ('Name', 4): {
            ('Name', 12): 1,
            ('Name', 7): 1,
            ('Name', 4): 1,
            ('Name', 6): 1,
            ('Name', 5): 1
        },
        # len
        ('AST', 'len'): {('Name', 5): 1, ('AST', 'len'): 1},
        # collection
        ('arg', 1): {
            ('Name', 9): 2,
            ('Name', 5): 1,
            ('Name', 6): 1,
            ('Name', 13): 1,
            ('arg', 1): 1,
            ('Name', 11): 1,
            ('Name', 8): 1
        },
        # j
        ('Name', 7): {
            ('Name', 8): 2,
            ('Name', 9): 2,
            ('Name', 11): 1,
            ('Name', 7): 1,
            ('Name', 10): 1
        },
        # temp
        ('Name', 6): {
            ('Name', 8): 1,
            ('Name', 6): 1,
            ('Name', 11): 1
        },
        # x (global)
        ('AST', -1): {('AST', -1): 1, ('Name', 18): 1, ('Global', 17): 1},
        # global_randint
        ('alias', 22): {('alias', 22): 1, ('Name', 49): 1},
        # choice
        ('alias', 23): {('alias', 23): 1, ('Name', 51): 1},
        # update_counter (global)
        ('FunctionDef', 25): {('Name', 28): 1, ('FunctionDef', 25): 1, ('Name', 72): 1},
        # global_counter
        ('Name', 26): {
            ('Name', 33): 1,
            ('Name', 55): 1,
            ('Global', 45): 1,
            ('Name', 26): 1,
            ('Name', 62): 1
        },
        # Counter
        ('ClassDef', 29): {('Name', 71): 1, ('ClassDef', 29): 1},
        # self of __init__
        ('arg', 30): {('Name', 32): 1, ('arg', 30): 1},
        # Counter.global_counter
        ('Name', 33): {
            ('Name', 33): 1,
            ('Name', 69): 1
        },
        # Counter.update_counter
        ('FunctionDef', 34): {('Name', 68): 1, ('FunctionDef', 34): 1},
        # method_counter
        ('Name', 39): {
            ('Name', 54): 1,
            ('Name', 61): 1,
            ('Nonlocal', 43): 1,
            ('Name', 39): 1
        },
        # increment (function)
        ('FunctionDef', 41): {('Name', 67): 1, ('FunctionDef', 41): 1},
        # increment (variable)
        ('Name', 49): {
            ('Name', 54): 1,
            ('Name', 56): 1,
            ('Name', 55): 1,
            ('Name', 61): 1,
            ('Name', 49): 1
        },
        # self (of update_counter)
        ('arg', 34): {('Name', 62): 1, ('Name', 56): 1, ('arg', 34): 1},
        # time
        ('alias', 36): {('alias', 36): 1, ('Name', 59): 1},
        # print
        ('AST', 'print'): {
            ('Name', 62): 1,
            ('AST', 'print'): 1,
            ('Name', 61): 1,
            ('Name', 65): 1,
            ('Name', 68): 1,
            ('Name', 69): 1
        },
        # ValueError
        ('AST', 'ValueError'): {('Name', 64): 1, ('Name', 52): 1, ('AST', 'ValueError'): 1},
        # e
        ('ExceptHandler', 64): {('Name', 65): 1, ('ExceptHandler', 64): 1},
    }

    assert GROUND_TRUTH_TRANSFORMED_DEFINE_TO_USES == transformed_define_to_uses
