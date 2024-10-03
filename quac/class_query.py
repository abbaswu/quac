import collections.abc
import contextlib
import logging
import numbers
import types
import typing

import numpy as np
import pandas as pd

from get_attributes_in_runtime_class import get_attributes_in_runtime_class
from get_attributes_in_typeshed_class_definition import get_attributes_in_typeshed_class_definition
from ignored_attributes import IGNORED_ATTRIBUTES
from iterate_inheritance_graph_layers import iterate_inheritance_graph_layers
from set_trie import SetTrieNode, add, contains
from type_definitions import RuntimeClass
from typeshed_client_ex.client import Client
from typeshed_client_ex.type_definitions import TypeshedClass, from_runtime_class

EXCLUDED_MODULE_NAMES = {
    '_typeshed', # We cover its relevant abstract base classes
    'typing', # We cover its relevant abstract base classes
    'typing_extensions', # We cover its relevant abstract base classes
    'builtins', # We cover its relevant concrete classes
    'types', # We cover its relevant concrete classes
    'collections.abc', # We cover its relevant abstract base classes
    'numbers', # We cover its relevant abstract base classes
    'contextlib', # We cover its relevant abstract base classes
    'io', # We cover its relevant abstract base classes through `typing.IO`
}


def initialize_class_query_database(
        runtime_classes: typing.AbstractSet[RuntimeClass],
        typeshed_client: Client
):
    attribute_set_trie_root: SetTrieNode[str] = SetTrieNode()
    typeshed_class_to_attribute_set_dict: dict[TypeshedClass, set[str]] = {}

    # Special handling for classes in `_typeshed` (Typeshed only)
    for typeshed_class in (
            TypeshedClass('_typeshed', 'SupportsItemAccess'),
            TypeshedClass('_typeshed', 'SupportsGetItem'),
            TypeshedClass('_typeshed', 'HasFileno'),
            TypeshedClass('_typeshed', 'SupportsRead'),
            TypeshedClass('_typeshed', 'SupportsReadline'),
            TypeshedClass('_typeshed', 'SupportsNoArgReadline'),
            TypeshedClass('_typeshed', 'SupportsWrite'),
            TypeshedClass('_typeshed', 'SupportsAdd'),
            TypeshedClass('_typeshed', 'SupportsRAdd'),
            TypeshedClass('_typeshed', 'SupportsSub'),
            TypeshedClass('_typeshed', 'SupportsRSub'),
            TypeshedClass('_typeshed', 'SupportsDivMod'),
            TypeshedClass('_typeshed', 'SupportsRDivMod'),
            TypeshedClass('_typeshed', 'SupportsTrunc'),
    ):
        typeshed_class_definition = typeshed_client.get_class_definition(typeshed_class)
        attributes_in_typeshed_class = get_attributes_in_typeshed_class_definition(typeshed_class_definition) - IGNORED_ATTRIBUTES
        add(attribute_set_trie_root, attributes_in_typeshed_class)
        typeshed_class_to_attribute_set_dict[typeshed_class] = attributes_in_typeshed_class

    # Special handling for byte sequences
    bytestring_typeshed_class = TypeshedClass('typing', 'ByteString')
    bytestring_attributes = get_attributes_in_runtime_class(bytes) | get_attributes_in_runtime_class(bytearray)
    add(attribute_set_trie_root, bytestring_attributes)
    typeshed_class_to_attribute_set_dict[bytestring_typeshed_class] = bytestring_attributes

    # Special handling for built-in types and abstract base types
    for runtime_class in (
            object,
            int,
            float,
            complex,
            list,
            str,
            set,
            frozenset,
            dict,
            tuple,
            range,
            slice,
            type,
            types.CellType,
            types.TracebackType,
            types.FrameType,
            types.CodeType,
            typing.SupportsIndex,
            typing.SupportsBytes,
            typing.SupportsComplex,
            typing.SupportsFloat,
            typing.SupportsInt,
            typing.SupportsRound,
            typing.SupportsAbs,
            typing.TextIO,
            typing.IO,
            collections.abc.Iterable,
            collections.abc.Collection,
            collections.abc.Iterator,
            collections.abc.Reversible,
            collections.abc.Generator,
            collections.abc.AsyncIterable,
            collections.abc.AsyncIterator,
            collections.abc.AsyncGenerator,
            collections.abc.Awaitable,
            collections.abc.Coroutine,
            collections.abc.Sequence,
            collections.abc.MutableSequence,
            collections.abc.Mapping,
            collections.abc.MutableMapping,
            collections.abc.Set,
            collections.abc.MutableSet,
            collections.abc.Callable,
            numbers.Complex,
            numbers.Real,
            numbers.Rational,
            numbers.Integral,
            contextlib.AbstractContextManager,
            contextlib.AbstractAsyncContextManager
    ):
        attributes_in_runtime_class = get_attributes_in_runtime_class(runtime_class)
        add(attribute_set_trie_root, attributes_in_runtime_class)
        typeshed_class = from_runtime_class(runtime_class)
        typeshed_class_to_attribute_set_dict[typeshed_class] = attributes_in_runtime_class

    # Handle classes from user-defined and third-party modules
    for inheritance_graph_layer in iterate_inheritance_graph_layers(runtime_classes):
        logging.warning('%s', inheritance_graph_layer)

        included_runtime_classes_in_inheritance_graph_layer = set()

        for runtime_class in inheritance_graph_layer:
            module_name = getattr(runtime_class, '__module__', None)
            if not isinstance(module_name, str) or module_name in EXCLUDED_MODULE_NAMES or module_name.startswith('_'):
                logging.warning('Excluded runtime class %s', runtime_class)
            else:
                attributes_in_runtime_class = get_attributes_in_runtime_class(runtime_class)

                if contains(attribute_set_trie_root, attributes_in_runtime_class):
                    logging.warning('Excluded runtime class %s from class query database as an existing class its attribute set', runtime_class)
                else:
                    logging.warning('Adding runtime class %s', runtime_class)
                    included_runtime_classes_in_inheritance_graph_layer.add(runtime_class)
        
        for included_runtime_class in included_runtime_classes_in_inheritance_graph_layer:
            attributes_in_runtime_class = get_attributes_in_runtime_class(included_runtime_class)
            add(attribute_set_trie_root, attributes_in_runtime_class)
            typeshed_class = from_runtime_class(included_runtime_class)
            typeshed_class_to_attribute_set_dict[typeshed_class] = attributes_in_runtime_class

    # Finish adding all classes
    candidate_class_list = list(typeshed_class_to_attribute_set_dict.keys())

    attribute_set = set.union(*typeshed_class_to_attribute_set_dict.values())
    attribute_list = list(attribute_set)

    class_attribute_matrix = pd.DataFrame(
        [
            [
                (attribute in typeshed_class_to_attribute_set_dict.get(candidate_class, set()))
                for attribute in attribute_list
            ]
            for candidate_class in candidate_class_list
        ],
        index=candidate_class_list,
        columns=attribute_list
    )

    # Count non-zero values in each column (Document Frequency)
    doc_frequency: pd.Series = class_attribute_matrix.apply(
        lambda attribute_column: (attribute_column != 0).sum()
    )

    # Calculate IDFs for each attribute
    idfs: pd.Series = np.log((len(candidate_class_list) - doc_frequency + 0.5) / (doc_frequency + 0.5) + 1)

    # Calculate the average number of attributes in all classes
    average_num_attributes_in_classes: float = (class_attribute_matrix != 0).sum(axis=1).mean()

    return (
        class_attribute_matrix,
        idfs,
        average_num_attributes_in_classes
    )


def get_score_function(
    attributes: typing.Iterable[str],
    idfs: typing.Mapping[str, float],
    average_num_attributes_in_classes: float
):
    k_1 = 1.5
    b = 0.75

    def score_function(class_row: pd.Series):
        num_attributes_in_class = (class_row != 0).sum()
        
        def attribute_score(attribute: str):
            attribute_idf = idfs.get(attribute, 0)
            attribute_frequency = class_row.get(attribute, 0)
            return attribute_idf * (attribute_frequency * (k_1 + 1)) / (attribute_frequency + k_1 * (1 - b + b * (num_attributes_in_class) / average_num_attributes_in_classes))

        return sum(
            map(attribute_score, attributes),
            0
        )
    
    return score_function


# Query TypeshedClass's given an attribute set.
def query(
    attribute_set: typing.AbstractSet[str],
    class_attribute_matrix: pd.DataFrame,
    idfs: typing.Mapping[str, float],
    average_num_attributes_in_classes: float
) -> tuple[np.ndarray, np.ndarray]:
    if attribute_set:
        score_function = get_score_function(attribute_set, idfs, average_num_attributes_in_classes)
        result_series = class_attribute_matrix.apply(score_function, axis=1)

        # Use numpy.argsort() on the Series values
        indices = np.argsort(result_series.values)[::-1]

        class_ndarray = class_attribute_matrix.index.values[indices]
        similarity_ndarray = result_series.values[indices]

        if (max_similarity := similarity_ndarray[0]) > 0.:
            return class_ndarray, similarity_ndarray

    # Either an empty attribute set, or no non-zero similarities calculated
    class_ndarray = np.zeros(0, dtype=object)
    similarity_ndarray = np.zeros(0)

    return class_ndarray, similarity_ndarray
