"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=handle_local_syntax_directed_typing_constraints test_handle_local_syntax_directed_typing_constraints.py
- Generate an HTML report: coverage html
"""

import builtins

from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings
from get_function_definitions_to_parameters_name_parameter_mappings_and_return_values import get_function_definitions_to_parameters_name_parameter_mappings_and_return_values
from get_use_define_mapping import get_use_define_mapping
from handle_local_syntax_directed_typing_constraints import handle_local_syntax_directed_typing_constraints
from relations import RelationType
from typeshed_client_ex.client import Client
from type_definitions import *
from unwrap import unwrap

from test_modules import all_syntax_constructs

module = all_syntax_constructs
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

function_definitions_to_parameters_name_parameter_mappings_and_return_values = get_function_definitions_to_parameters_name_parameter_mappings_and_return_values(
    [module_node]
)

### STATEFUL SECTION

names_to_dummy_definition_nodes = {}

typeshed_client = Client()

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

node_relations = set()

def add_relation(first: ast.AST, second: ast.AST, relation_type: RelationType, parameter: typing.Optional[object]):
    node_relations.add((first, second, relation_type, parameter))

for key, value in builtins.__dict__.items():
    name = key
    unwrapped_value = unwrap(value)
    if (not name.startswith('_')) and isinstance(unwrapped_value, (RuntimeClass, UnwrappedRuntimeFunction)):
        dummy_definition_node = ast.AST()
        setattr(dummy_definition_node, 'id', name)
        names_to_dummy_definition_nodes[name] = dummy_definition_node

        if isinstance(unwrapped_value, RuntimeClass):
            update_runtime_terms(dummy_definition_node, {unwrapped_value})
        elif isinstance(unwrapped_value, UnwrappedRuntimeFunction):
            update_runtime_terms(dummy_definition_node, {runtime_term_of_unwrapped_runtime_function(unwrapped_value)})

for value in (True, False, Ellipsis, None, NotImplemented):
    name = str(value)
    dummy_definition_node = ast.AST()
    setattr(dummy_definition_node, 'id', name)
    names_to_dummy_definition_nodes[name] = dummy_definition_node

use_define_mapping = get_use_define_mapping(
    module_node,
    names_to_dummy_definition_nodes
)

node_to_definition_node_mapping = {
    node: definition_node
    for definition_node, nodes in use_define_mapping.itersets()
    for node in nodes
}

handle_local_syntax_directed_typing_constraints(
    module_node,
    top_level_class_definitions_to_runtime_classes,
    unwrapped_runtime_functions_to_named_function_definitions,
    function_definitions_to_parameters_name_parameter_mappings_and_return_values,
    node_to_definition_node_mapping,
    get_runtime_terms,
    update_runtime_terms,
    update_bag_of_attributes,
    add_subset,
    add_relation,
    typeshed_client
)

def transform_node(node: ast.AST):
    return (
        getattr(type(node), '__name__', ''),
        getattr(node, 'lineno', -1),
        getattr(node, 'col_offset', -1),
        getattr(node, 'end_lineno', -1),
        getattr(node, 'end_col_offset', -1),
        getattr(node, 'id', '')
    )

from print_dict import pd

node_to_runtime_items = {
    transform_node(k): v
    for k, v in node_runtime_terms.items()
}

superset_to_subset = {}

for superset, subset in node_subsets:
    superset_to_subset.setdefault(
        transform_node(superset),
        set()
    ).add(transform_node(subset))

node_to_related_node_to_relation = {}

for first, second, relation_type, parameter in node_relations:
    node_to_related_node_to_relation.setdefault(
        transform_node(first),
        dict()
    ).setdefault(
        transform_node(second),
        set()
    ).add(
        (
            relation_type, parameter
        )
    )
