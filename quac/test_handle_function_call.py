"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=handle_function_call test_handle_function_call.py
- Generate an HTML report: coverage html
"""

import ast
import typing

from get_attribute_access_result import get_attribute_access_result
from get_attributes_in_runtime_class import get_attributes_in_runtime_class
from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings
from get_function_definitions_to_parameters_name_parameter_mappings_and_return_values import get_function_definitions_to_parameters_name_parameter_mappings_and_return_values
from handle_function_call import handle_function_call
from typeshed_client_ex.client import Client
from type_definitions import (
    RuntimeTerm,
    Module,
    RuntimeClass,
    Instance,
    UnwrappedRuntimeFunction,
    FunctionDefinition,
    UnboundMethod,
    BoundMethod
)


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

    function_definitions_to_parameters_name_parameter_mappings_and_return_values = get_function_definitions_to_parameters_name_parameter_mappings_and_return_values([module_node])

    typeshed_client = Client()


    # Call user-defined class
    apparent_arguments = []
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            module.OuterClass,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {returned_value: {Instance(module.OuterClass)}}
    assert node_bags_of_attributes == {returned_value: get_attributes_in_runtime_class(module.OuterClass)}
    assert not node_subsets


    # Call built-in class
    import csv
    import collections.abc

    first_argument = ast.AST()
    apparent_arguments = [first_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            csv.DictReader,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {first_argument: {Instance(collections.abc.Iterable)}, returned_value: {Instance(csv.DictReader)}}
    assert node_bags_of_attributes == {first_argument: get_attributes_in_runtime_class(collections.abc.Iterable), returned_value: get_attributes_in_runtime_class(csv.DictReader)}
    assert not node_subsets


    # Call built-in function
    first_argument = ast.AST()
    apparent_arguments = [first_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            len,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {first_argument: {Instance(collections.abc.Sized)}, returned_value: {Instance(int)}}
    assert node_bags_of_attributes == {first_argument: get_attributes_in_runtime_class(collections.abc.Sized), returned_value: get_attributes_in_runtime_class(int)}
    assert not node_subsets


    # Call built-in special function hasattr
    first_argument = ast.AST()
    second_argument = ast.parse("'attr'").body[0].value

    apparent_arguments = [first_argument, second_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            hasattr,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {returned_value: {Instance(bool)}}
    assert node_bags_of_attributes == {first_argument: {'attr'}, returned_value: get_attributes_in_runtime_class(bool)}
    assert not node_subsets


    # Call built-in special function open
    first_argument = ast.AST()
    second_argument = ast.AST()

    apparent_arguments = [first_argument, second_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            open,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {first_argument: {Instance(str)}, second_argument: {Instance(str)}, returned_value: {Instance(typing.IO)}}
    assert node_bags_of_attributes == {first_argument: get_attributes_in_runtime_class(str), second_argument: get_attributes_in_runtime_class(str), returned_value: get_attributes_in_runtime_class(typing.IO)}
    assert not node_subsets


    # Call user-defined function by name
    named_function_definition = unwrapped_runtime_functions_to_named_function_definitions[
        nested_class_and_nested_async_function.fetch_and_process
    ]

    first_argument = ast.AST()

    apparent_arguments = []
    names_to_arguments = {"url_fetcher": first_argument}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
        named_function_definition,
        apparent_arguments,
        names_to_arguments,
        returned_value,
        unwrapped_runtime_functions_to_named_function_definitions,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values,
        get_runtime_terms,
        update_runtime_terms,
        update_bag_of_attributes,
        add_subset,
        typeshed_client,
    )

    assert not node_runtime_terms
    assert not node_bags_of_attributes

    parameters, _, return_value = function_definitions_to_parameters_name_parameter_mappings_and_return_values[named_function_definition]

    assert node_subsets == {(first_argument, parameters[0]), (returned_value, return_value)}


    # Call user-defined unbound method by name
    unbound_method = get_attribute_access_result(
        nested_class_and_nested_async_function.OuterClass,
        'get_url',
        unwrapped_runtime_functions_to_named_function_definitions
    )

    apparent_arguments = []
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
        unbound_method,
        apparent_arguments,
        names_to_arguments,
        returned_value,
        unwrapped_runtime_functions_to_named_function_definitions,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values,
        get_runtime_terms,
        update_runtime_terms,
        update_bag_of_attributes,
        add_subset,
        typeshed_client,
    )

    assert not node_runtime_terms
    assert not node_bags_of_attributes

    parameters, _, return_value = function_definitions_to_parameters_name_parameter_mappings_and_return_values[unbound_method.function]

    assert node_subsets == {(returned_value, return_value)}


    # Call instance
    import symtable
    instance = Instance(symtable.SymbolTableFactory)

    """
    class SymbolTableFactory:
        def new(self, table: Any, filename: str) -> SymbolTable: ...
        def __call__(self, table: Any, filename: str) -> SymbolTable: ...
    """

    first_argument = ast.AST()
    second_argument = ast.AST()

    apparent_arguments = [first_argument, second_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
        instance,
        apparent_arguments,
        names_to_arguments,
        returned_value,
        unwrapped_runtime_functions_to_named_function_definitions,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values,
        get_runtime_terms,
        update_runtime_terms,
        update_bag_of_attributes,
        add_subset,
        typeshed_client,
    )

    assert node_runtime_terms == {
        second_argument: {Instance(str)},
        returned_value: {Instance(symtable.SymbolTable)}
    }

    assert node_bags_of_attributes == {
        second_argument: get_attributes_in_runtime_class(str),
        returned_value: get_attributes_in_runtime_class(symtable.SymbolTable)
    }

    assert not node_subsets


    # Call method
    method = get_attribute_access_result(instance, 'new', unwrapped_runtime_functions_to_named_function_definitions)

    """
    class SymbolTableFactory:
        def new(self, table: Any, filename: str) -> SymbolTable: ...
        def __call__(self, table: Any, filename: str) -> SymbolTable: ...
    """

    first_argument = ast.AST()
    second_argument = ast.AST()

    apparent_arguments = [first_argument, second_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
        method,
        apparent_arguments,
        names_to_arguments,
        returned_value,
        unwrapped_runtime_functions_to_named_function_definitions,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values,
        get_runtime_terms,
        update_runtime_terms,
        update_bag_of_attributes,
        add_subset,
        typeshed_client,
    )

    assert node_runtime_terms == {
        second_argument: {Instance(str)},
        returned_value: {Instance(symtable.SymbolTable)}
    }

    assert node_bags_of_attributes == {
        second_argument: get_attributes_in_runtime_class(str),
        returned_value: get_attributes_in_runtime_class(symtable.SymbolTable)
    }

    assert not node_subsets


    # Call user-defined method
    instance = Instance(nested_class_and_nested_async_function.OuterClass)
    method = get_attribute_access_result(instance, 'outer_method', unwrapped_runtime_functions_to_named_function_definitions)

    """
    class OuterClass:
        def outer_method(self):
            def nested_function_1():
                print("Inside nested_function_1")

                def deeply_nested_function():
                    print("Inside deeply_nested_function")

                deeply_nested_function()
    """

    # NOTE: These are redundant.
    first_argument = ast.AST()
    second_argument = ast.AST()

    apparent_arguments = [first_argument, second_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
        method,
        apparent_arguments,
        names_to_arguments,
        returned_value,
        unwrapped_runtime_functions_to_named_function_definitions,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values,
        get_runtime_terms,
        update_runtime_terms,
        update_bag_of_attributes,
        add_subset,
        typeshed_client,
    )

    assert not node_runtime_terms
    assert not node_bags_of_attributes

    parameters, _, return_value = function_definitions_to_parameters_name_parameter_mappings_and_return_values[method.function]

    assert node_subsets == {(returned_value, return_value)}


    # Call built-in function not in Typeshed
    import numpy as np


    first_argument = ast.AST()
    apparent_arguments = [first_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            np.zeros,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert not node_runtime_terms
    assert not node_bags_of_attributes
    assert not node_subsets


    # Call built-in type not in Typeshed
    import pandas as pd

    first_argument = ast.AST()
    apparent_arguments = [first_argument]
    names_to_arguments = {}
    returned_value = ast.AST()

    node_runtime_terms = {}

    def get_runtime_terms(node: ast.AST):
        return node_runtime_terms.get(node, set())

    def update_runtime_terms(node: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node, set()).update(attributes)

    node_subsets = set()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subsets.add((superset, subset))

    handle_function_call(
            pd.DataFrame,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            unwrapped_runtime_functions_to_named_function_definitions,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            get_runtime_terms,
            update_runtime_terms,
            update_bag_of_attributes,
            add_subset,
            typeshed_client,
    )

    assert node_runtime_terms == {returned_value: {Instance(pd.DataFrame)}}
    assert node_bags_of_attributes == {returned_value: get_attributes_in_runtime_class(pd.DataFrame)}
    assert not node_subsets
