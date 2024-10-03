import argparse
import builtins
import importlib
import json
import logging
import os
import os.path
import sys
import types
import typing

import networkx as nx

from ast_node_namespace_trie import get_ast_node_namespace_trie, search_ast_node_namespace_trie
from class_query import *
from get_definitions_to_runtime_terms_mappings import get_definitions_to_runtime_terms_mappings
from get_function_definitions_to_parameters_name_parameter_mappings_and_return_values import get_function_definitions_to_parameters_name_parameter_mappings_and_return_values
from get_module_names_to_imported_names_to_runtime_objects import get_module_names_to_imported_names_to_runtime_objects
from get_use_define_mapping import get_use_define_mapping
from get_types_in_module import get_types_in_module
from get_typing_slots_in_query_dict import get_typing_slots_in_query_dict
from handle_local_syntax_directed_typing_constraints import handle_local_syntax_directed_typing_constraints
from query_result_dict import QueryDict, generate_query_dict
from relations import RelationType
from static_import_analysis import do_static_import_analysis
from trie import search
from typeshed_client_ex.client import Client
from typeshed_client_ex.type_definitions import TypeshedClass
from type_definitions import *
from type_inference import get_type_inference_function
from unwrap import unwrap


if __name__ == '__main__':
    sys.setrecursionlimit(65536)

    # Set up logging
    # https://stackoverflow.com/questions/10973362/python-logging-function-name-file-name-line-number-using-a-single-file
    FORMAT = '[%(asctime)s %(filename)s %(funcName)s():%(lineno)s]%(levelname)s: %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.WARNING)

    # Parse command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--module-search-path', type=str, required=True, help='Module search path')
    parser.add_argument('-p', '--module-prefix', type=str, required=True, help='Module prefix')
    parser.add_argument('-o', '--output-file', type=str, required=False, default='output.json', help='Output JSON file')
    args = parser.parse_args()

    # Search modules

    module_search_absolute_path: str = os.path.abspath(args.module_search_path)
    module_prefix: str = args.module_prefix

    (
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict,
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict
    ) = do_static_import_analysis(module_search_absolute_path, module_prefix)

    output_file: str = args.output_file

    # Generate query dict
    query_dict: QueryDict = generate_query_dict(
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict
    )

    # Import modules

    module_name_to_module_node = {}
    module_name_to_module = {}

    sys.path.insert(0, module_search_absolute_path)

    for module_name, file_path in module_name_to_file_path_dict.items():
        try:
            with open(file_path, 'r') as fp:
                code = fp.read()
                module_node = ast.parse(code)
            
            module = importlib.import_module(module_name)

            module_name_to_module_node[module_name] = module_node
            module_name_to_module[module_name] = module
        except (ImportError, UnicodeError):
            logging.exception('Failed to import module %s', module_name)

    module_names = list(module_name_to_module_node.keys())
    module_nodes = list(module_name_to_module_node.values())
    modules = list(module_name_to_module.values())

    # Get information from all modules

    module_names_to_imported_names_to_runtime_objects = get_module_names_to_imported_names_to_runtime_objects(
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict,
        module_name_to_module
    )

    (
        top_level_class_definitions_to_runtime_classes,
        unwrapped_runtime_functions_to_named_function_definitions
    ) = get_definitions_to_runtime_terms_mappings(
        module_names,
        modules,
        module_nodes
    )

    function_definitions_to_parameters_name_parameter_mappings_and_return_values = get_function_definitions_to_parameters_name_parameter_mappings_and_return_values(
        module_nodes
    )

    ast_node_namespace_trie_root = get_ast_node_namespace_trie(
        module_names,
        module_nodes,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values
    )

    # Initialize class query database

    client = Client()

    runtime_classes = set()

    for module_name, module in module_name_to_module.items():        
        for runtime_class in get_types_in_module(module):
            runtime_classes.add(runtime_class)
        
    for module_name, import_tuple_set in module_name_to_import_tuple_set_dict.items():
        for imported_module_name, imported_module_name_alias in import_tuple_set:
            if imported_module_name in sys.modules:
                imported_module = sys.modules[imported_module_name]
                if isinstance(imported_module, types.ModuleType):
                    for runtime_class in get_types_in_module(imported_module):
                        runtime_classes.add(runtime_class)

    for module_name, import_from_tuple_set in module_name_to_import_from_tuple_set_dict.items():
        for import_from_module_name, imported_name, imported_name_alias in import_from_tuple_set:
            if import_from_module_name in sys.modules:
                import_from_module = sys.modules[import_from_module_name]
                if isinstance(import_from_module, types.ModuleType):
                    value = getattr(import_from_module, imported_name, None)
                    if isinstance(value, type):
                        runtime_classes.add(value)

    (
        class_attribute_matrix,
        idfs,
        average_num_attributes_in_classes
    ) = initialize_class_query_database(runtime_classes, client)

    # STATEFUL SECTION

    node_runtime_terms = {}

    def get_runtime_terms(node_: ast.AST):
        return node_runtime_terms.get(node_, set())

    def update_runtime_terms(node_: ast.AST, runtime_terms: typing.Iterable[RuntimeTerm]):
        node_runtime_terms.setdefault(node_, set()).update(runtime_terms)

    node_bags_of_attributes = {}

    def update_bag_of_attributes(node_: ast.AST, attributes: typing.Iterable[str]):
        node_bags_of_attributes.setdefault(node_, set()).update(attributes)

    def get_bag_of_attributes(node_: ast.AST):
        return node_bags_of_attributes.get(node_, set())

    node_subset_graph = nx.DiGraph()

    def add_subset(superset: ast.AST, subset: ast.AST):
        node_subset_graph.add_edge(superset, subset)

    def set_equivalent(
        first: ast.AST,
        second: ast.AST
    ):
        add_subset(first, second)
        add_subset(second, first)

    def get_subset_nodes(node_: ast.AST):
        if node_ in node_subset_graph:
            # Get all nodes reachable from the start node using DFS
            return frozenset(nx.dfs_preorder_nodes(node_subset_graph, node_))
        else:
            return frozenset((node_,))

    node_relations: dict[
        ast.AST,
        dict[
            RelationType,
            dict[
                typing.Optional[object],
                set[ast.AST]
            ]
        ]
    ] = {}

    def add_relation(first: ast.AST, second: ast.AST, relation_type: RelationType, parameter: typing.Optional[object]):
        node_relations.setdefault(first, {}).setdefault(relation_type, {}).setdefault(parameter, set()).add(second)

    def get_relations(node_: ast.AST):
        return node_relations.get(node_, {})

    # Handle each module

    for module_name, module_node in module_name_to_module_node.items():
        # Initialize dummy definition nodes with builtins and imports
        names_to_dummy_definition_nodes = {}

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
            update_runtime_terms(dummy_definition_node, {Instance(type(value))})

        imported_names_to_runtime_objects = module_names_to_imported_names_to_runtime_objects.get(module_name, {})
        for imported_name, runtime_object in imported_names_to_runtime_objects.items():
            unwrapped_runtime_object = unwrap(runtime_object)
            runtime_term: typing.Optional[RuntimeTerm] = None

            if isinstance(unwrapped_runtime_object, Module):
                runtime_term = unwrapped_runtime_object
            elif isinstance(unwrapped_runtime_object, RuntimeClass):
                runtime_term = unwrapped_runtime_object
            elif isinstance(unwrapped_runtime_object, UnwrappedRuntimeFunction):
                processed_unwrapped_runtime_object = runtime_term_of_unwrapped_runtime_function(unwrapped_runtime_object)

                runtime_term = unwrapped_runtime_functions_to_named_function_definitions.get(
                    processed_unwrapped_runtime_object,
                    processed_unwrapped_runtime_object
                )
            
            if runtime_term is not None:
                dummy_definition_node = ast.AST()
                setattr(dummy_definition_node, 'id', imported_name)

                names_to_dummy_definition_nodes[imported_name] = dummy_definition_node
                update_runtime_terms(dummy_definition_node, {runtime_term})
            else:
                logging.error(
                    'Cannot match imported name %s in module %s with unwrapped runtime object %s to a runtime term!',
                    imported_name, module_name, unwrapped_runtime_object
                )

        use_define_mapping = get_use_define_mapping(
            module_node,
            names_to_dummy_definition_nodes
        )

        node_to_definition_node_mapping = {
            node: definition_node
            for definition_node, nodes in use_define_mapping.itersets()
            for node in nodes
        }

        for node, definition_node in node_to_definition_node_mapping.items():
            set_equivalent(definition_node, node)

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
            client
        )

    # Get type inference function

    type_inference_function = get_type_inference_function(
        get_runtime_terms,
        get_bag_of_attributes,
        get_subset_nodes,
        get_relations,
        client,
        class_attribute_matrix,
        idfs,
        average_num_attributes_in_classes
    )

    # Perform type inference

    class_inference_failed_fallback: TypeshedClass = TypeshedClass('typing', 'Any')

    output_dict: dict[
        str, # module_name
        dict[
            str, # class_name_or_global
            dict[
                str, # function_name
                dict[
                    str, # parameter_name_or_return
                    list[
                        str # type_inference_result
                    ]
                ]
            ]
        ]
    ] = {}

    for (
        module_name_,
        class_name_or_global_,
        function_name_,
        parameter_name_or_return_
    ) in get_typing_slots_in_query_dict(query_dict):
        if class_name_or_global_ == 'global':
            components = [module_name_, function_name_, parameter_name_or_return_]
        else:
            components = [module_name_, class_name_or_global_, function_name_, parameter_name_or_return_]
        
        node_set = search_ast_node_namespace_trie(ast_node_namespace_trie_root, components)

        type_inference_result_list = output_dict.setdefault(module_name_, {}).setdefault(class_name_or_global_, {}).setdefault(function_name_, {}).setdefault(parameter_name_or_return_, [])

        # Do not infer parameter types for self and cls in methods of classes.
        # Do not infer return types for __init__ and __new__ of classes.
        if (
            (class_name_or_global_ != 'global' and parameter_name_or_return_ in ('self', 'cls'))
            or (class_name_or_global_ != 'global' and function_name_ in ('__init__', '__new__') and parameter_name_or_return_ == 'return')
        ):
            continue

        type_inference_result = type_inference_function(node_set, class_inference_failed_fallback=class_inference_failed_fallback)

        if type_inference_result != class_inference_failed_fallback:
            type_inference_result_list.append(str(type_inference_result))

    with open(output_file, 'w') as output_file_io:
        json.dump(output_dict, output_file_io, indent=4)
