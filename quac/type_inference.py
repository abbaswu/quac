import ast
import json
import logging
import typing

import numpy as np
import pandas as pd

from class_query import query
from get_attributes_in_runtime_class import get_attributes_in_runtime_class
from get_number_of_type_variables import get_number_of_type_variables
from get_relation_sets_of_type_parameters import get_relation_sets_of_type_parameters
from relations import RelationType
from type_definitions import Instance, RuntimeClass, RuntimeTerm
from typeshed_client_ex.client import Client
from typeshed_client_ex.type_definitions import (
    TypeshedTypeAnnotation,
    TypeshedClass,
    from_runtime_class,
    subscribe
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


def dump_confidence_and_possible_class_list(
        confidence_and_possible_class_list: list[tuple[float, TypeshedClass]],
        class_inference_log_file_io: typing.IO
):
    confidence_and_possible_class_string_list_list: list[list[typing.Union[float, str]]] = [
        [confidence, str(possible_class)]
        for confidence, possible_class in confidence_and_possible_class_list
    ]

    json.dump(confidence_and_possible_class_string_list_list, class_inference_log_file_io)
    class_inference_log_file_io.write('\n')


def query_relation_sets_of_type_parameters(
    top_class_prediction: TypeshedClass,
    augmented_node_set: typing.AbstractSet[ast.AST],
    get_relations_callback: typing.Callable[
        [ast.AST],
        typing.Mapping[
            RelationType,
            typing.Mapping[
                typing.Optional[object],
                typing.AbstractSet[ast.AST]
            ]
        ]
    ],
    client: Client
):
    augmented_relations: dict[RelationType, dict[typing.Optional[object], set[ast.AST]]] = {}

    for node in augmented_node_set:
        relations = get_relations_callback(node)
        for relation_type, parameter_to_out_nodes in relations.items():
            for parameter, out_nodes in parameter_to_out_nodes.items():
                augmented_relations.setdefault(relation_type, {}).setdefault(parameter, set()).update(out_nodes)

    number_of_type_variables = get_number_of_type_variables(
        top_class_prediction,
        augmented_relations,
        client
    )

    return get_relation_sets_of_type_parameters(
        top_class_prediction,
        number_of_type_variables
    )


def get_all_nodes_related_by_relation_set(
    augmented_node_set: typing.AbstractSet[ast.AST],
    relation_set: typing.AbstractSet[tuple[RelationType, typing.Optional[object]]],
    get_relations_callback: typing.Callable[
        [ast.AST],
        typing.Mapping[
            RelationType,
            typing.Mapping[
                typing.Optional[object],
                typing.AbstractSet[ast.AST]
            ]
        ]
    ]
):
    all_related_nodes = set()
    for node in augmented_node_set:
        relations = get_relations_callback(node)

        for relation_type, parameter in relation_set:
            related_nodes = relations.get(relation_type, {}).get(parameter, set())
            all_related_nodes.update(related_nodes)

    return all_related_nodes


def get_type_inference_function(
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    get_bag_of_attributes_callback: typing.Callable[[ast.AST], typing.Iterable[str]],
    get_subset_nodes_callback: typing.Callable[[ast.AST], typing.Iterable[ast.AST]],
    get_relations_callback: typing.Callable[
        [ast.AST],
        typing.Mapping[
            RelationType,
            typing.Mapping[
                typing.Optional[object],
                typing.AbstractSet[ast.AST]
            ]
        ]
    ],
    client: Client,
    class_attribute_matrix: pd.DataFrame,
    idfs: pd.Series,
    average_num_attributes_in_classes: float
):
    class_inference_cache: dict[
        frozenset[ast.AST],
        tuple[
            list[tuple[float, TypeshedTypeAnnotation]],
            bool
        ]
    ] = {}
    
    type_inference_cache: dict[frozenset[ast.AST], TypeshedTypeAnnotation] = {}

    def infer_classes_for_augmented_node_set(
        augmented_node_set: frozenset[ast.AST],
        indent_level: int = 0,
        cosine_similarity_threshold: float = 1e-1
    ) -> tuple[
        list[tuple[float, TypeshedClass]],  # class inference confidences and classs
        bool  # whether runtime class can be instance-of types.NoneType
    ]:
        nonlocal class_inference_cache

        indent = '    ' * indent_level

        # Has a record in cache?
        if augmented_node_set in class_inference_cache:
            logging.info(
                '%sCache hit when performing class inference for %s.',
                indent,
                augmented_node_set
            )

            return class_inference_cache[augmented_node_set]
        else:
            # No record in cache
            logging.info(
                '%sCache miss when performing class inference for %s.',
                indent,
                augmented_node_set
            )

            # Determine whether it can be None.
            aggregate_runtime_term_set = set().union(
                *(get_runtime_terms_callback(node) for node in augmented_node_set)
            )

            aggregate_can_be_none: bool = False
            aggregate_non_none_runtime_classes: set[RuntimeClass] = set()

            for runtime_term in aggregate_runtime_term_set:
                if isinstance(runtime_term, Instance):
                    instance_class = runtime_term.class_
                    if instance_class is type(None):
                        aggregate_can_be_none = True
                    elif instance_class is not type(NotImplemented):
                        aggregate_non_none_runtime_classes.add(instance_class)

            logging.info(
                '%sAggregate non-None runtime classes for %s: %s',
                indent,
                augmented_node_set, aggregate_non_none_runtime_classes
            )

            logging.info(
                '%sCan %s be None? %s',
                indent,
                augmented_node_set, aggregate_can_be_none
            )

            # Initialize aggregate attribute set.

            aggregate_attribute_set = set().union(
                *(get_bag_of_attributes_callback(node) for node in augmented_node_set)
            )

            logging.info(
                '%sAggregate attribute set for %s: %s',
                indent,
                augmented_node_set, aggregate_attribute_set
            )

            # Query possible classes.

            confidence_and_possible_class_list: list[tuple[float, TypeshedClass]] = []

            if (
                len(aggregate_non_none_runtime_classes) == 1
                and aggregate_attribute_set.issubset(
                    get_attributes_in_runtime_class(
                        single_runtime_class_covering_all_attributes := next(iter(aggregate_non_none_runtime_classes))
                    )
                )
            ):
                confidence_and_possible_class_list.append(
                    (1, from_runtime_class(single_runtime_class_covering_all_attributes))
                )

                logging.info(
                    '%sSingle runtime class covering all attributes for %s: %s',
                    indent,
                    augmented_node_set,
                    single_runtime_class_covering_all_attributes
                )
            else:
                (
                    possible_class_ndarray,
                    cosine_similarity_ndarray
                ) = query(
                    aggregate_attribute_set,
                    class_attribute_matrix,
                    idfs,
                    average_num_attributes_in_classes
                )

                nonzero_cosine_similarity_indices = (cosine_similarity_ndarray > cosine_similarity_threshold)

                selected_possible_class_ndarray = possible_class_ndarray[nonzero_cosine_similarity_indices]
                selected_cosine_similarity_ndarray = cosine_similarity_ndarray[nonzero_cosine_similarity_indices]

                argsort = np.argsort(selected_cosine_similarity_ndarray)

                for i in argsort[-1::-1]:
                    possible_class = selected_possible_class_ndarray[i]
                    cosine_similarity = float(selected_cosine_similarity_ndarray[i])

                    confidence_and_possible_class_list.append(
                        (cosine_similarity, possible_class)
                    )

                logging.info(
                    '%sPossible types queried for %s based on attributes: %s',
                    indent,
                    augmented_node_set,
                    confidence_and_possible_class_list
                )

            return_value = confidence_and_possible_class_list, aggregate_can_be_none

            class_inference_cache[augmented_node_set] = return_value

            return return_value

    def infer_type_for_node_set(
        node_set: frozenset[ast.AST],
        depth: int = 0,
        cosine_similarity_threshold: float = 1e-1,
        depth_limit: int = 3,
        class_inference_failed_fallback: TypeshedClass = TypeshedClass('typing', 'Any'),
        class_inference_log_file_io: typing.Optional[typing.IO] = None
    ) -> TypeshedTypeAnnotation:
        indent = '    ' * depth

        # Has a record in cache?
        if node_set in type_inference_cache:
            logging.info(
                '%sCache hit when performing type inference for %s.',
                indent,
                node_set
            )

            return type_inference_cache[node_set]
        else:
            # No record in cache
            logging.info(
                '%sCache miss when performing type inference for %s.',
                indent,
                node_set
            )

            if depth > depth_limit:
                logging.error(
                    '%sRecursive type inference exceeded depth limit of %s. Returning %s.',
                    indent,
                    depth_limit,
                    class_inference_failed_fallback
                )

                return_value = class_inference_failed_fallback
            else:
                logging.info(
                    '%sPerforming class inference for %s.',
                    indent,
                    node_set
                )

                # Part 0: Augment node set.
                augmented_node_set = frozenset().union(
                    *(get_subset_nodes_callback(node) for node in node_set)
                )

                logging.info(
                    '%sAugmented node set to %s.',
                    indent,
                    {transform_node(node) for node in augmented_node_set}
                )

                # Part 1: Infer possible classes.
                (
                    confidence_and_possible_class_list,
                    aggregate_can_be_none
                ) = infer_classes_for_augmented_node_set(
                    augmented_node_set,
                    depth + 1,
                    cosine_similarity_threshold
                )

                if class_inference_log_file_io is not None:
                    dump_confidence_and_possible_class_list(
                        confidence_and_possible_class_list,
                        class_inference_log_file_io
                    )

                # Part 2: Extract top class prediction.

                if not confidence_and_possible_class_list:
                    top_class_prediction = class_inference_failed_fallback

                    logging.info(
                        '%sNo possible classes queried for %s based on attributes. Using %s.',
                        indent,
                        augmented_node_set,
                        top_class_prediction
                    )
                else:
                    (
                        top_class_prediction_confidence,
                        top_class_prediction
                    ) = confidence_and_possible_class_list[0]

                    logging.info(
                        '%sTop class prediction: %s',
                        indent,
                        top_class_prediction
                    )

                # Part 3: Predict type parameters of top class prediction.

                type_parameter_type_prediction_list = []

                for relation_set in query_relation_sets_of_type_parameters(
                    top_class_prediction,
                    augmented_node_set,
                    get_relations_callback,
                    client
                ):
                    related_nodes = get_all_nodes_related_by_relation_set(
                        augmented_node_set,
                        relation_set,
                        get_relations_callback
                    )

                    type_parameter_type_prediction = infer_type_for_node_set(
                        frozenset(related_nodes),
                        depth + 1,
                        cosine_similarity_threshold,
                        depth_limit,
                        class_inference_failed_fallback,
                        class_inference_log_file_io
                    )
                    type_parameter_type_prediction_list.append(type_parameter_type_prediction)

                # Part 4: Get final type prediction.
                if type_parameter_type_prediction_list:
                    final_type_prediction = subscribe(top_class_prediction, tuple(type_parameter_type_prediction_list))
                else:
                    final_type_prediction = top_class_prediction

                return_value = final_type_prediction

            type_inference_cache[node_set] = return_value

            return return_value

    return infer_type_for_node_set
