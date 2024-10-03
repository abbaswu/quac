import logging
import typing

from relations import RelationType
from typeshed_client_ex.type_definitions import TypeshedClass


def get_relation_sets_of_type_parameters(
        subscribed_class: TypeshedClass,
        number_of_type_parameters: int = 0
) -> list[set[tuple[RelationType, typing.Optional[object]]]]:
    # Iterable-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf the node set.
    if subscribed_class in (
            TypeshedClass('typing', 'Iterable'),
            TypeshedClass('typing', 'Iterator'),
            TypeshedClass('typing', 'Container'),
            TypeshedClass('typing', 'Collection'),
            TypeshedClass('typing', 'AbstractSet'),
            TypeshedClass('typing', 'MutableSet'),
            TypeshedClass('typing', 'Reversible'),
            TypeshedClass('typing', 'KeysView'),
            TypeshedClass('typing', 'ValuesView'),
            TypeshedClass('typing', 'AsyncIterable'),
            TypeshedClass('typing', 'AsyncIterator'),
            TypeshedClass('builtins', 'set'),
            TypeshedClass('builtins', 'frozenset'),
            TypeshedClass('_collections_abc', 'dict_keys'),
            TypeshedClass('builtins', 'filter'),
            TypeshedClass('builtins', 'map'),
            TypeshedClass('builtins', 'reversed'),
            TypeshedClass('builtins', 'zip'),
            TypeshedClass('_typeshed', 'SupportsNext'),
            TypeshedClass('_typeshed', 'SupportsAnext'),
            TypeshedClass('itertools', 'count'),
            TypeshedClass('itertools', 'cycle'),
            TypeshedClass('itertools', 'repeat'),
            TypeshedClass('itertools', 'accumulate'),
            TypeshedClass('itertools', 'chain'),
            TypeshedClass('itertools', 'compress'),
            TypeshedClass('itertools', 'dropwhile'),
            TypeshedClass('itertools', 'filterfalse'),
            TypeshedClass('itertools', 'islice'),
            TypeshedClass('itertools', 'starmap'),
            TypeshedClass('itertools', 'takewhile'),
            TypeshedClass('itertools', 'zip_longest'),
            TypeshedClass('itertools', 'product'),
            TypeshedClass('itertools', 'combinations'),
            TypeshedClass('itertools', 'pairwise')
    ):
        return [{(RelationType.IterTargetOf, None)}]
    # dict_values
    # Ascribe <the second type annotation> to nodes which are IterTargetOf the node set.
    elif subscribed_class == TypeshedClass('_collections_abc', 'dict_values'):
        return [{}, {(RelationType.IterTargetOf, None)}]
    # SupportsGetItem-like
    # Ascribe <the first type annotation> to nodes which are KeyOf the node set.
    # Ascribe <the second type annotation> to nodes which are ValueOf the node set.
    elif subscribed_class in (
            TypeshedClass('_typeshed', 'SupportsGetItem'),
            TypeshedClass('_typeshed', 'SupportsItemAccess'),
    ):
        return [{(RelationType.KeyOf, None)}, {(RelationType.ValueOf, None)}]
    # Sequence-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf, ValueOf the node set.
    elif subscribed_class in (
            TypeshedClass('typing', 'Sequence'),
            TypeshedClass('typing', 'MutableSequence'),
            TypeshedClass('builtins', 'list'),
            TypeshedClass('collections', 'deque'),
            TypeshedClass('collections', 'UserList'),
            TypeshedClass('array', 'array'),
            TypeshedClass('_typeshed', 'SupportsLenAndGetItem')
    ):
        return [{(RelationType.IterTargetOf, None), (RelationType.ValueOf, None)}]
    # Mapping-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf, KeyOf the node set.
    # Ascribe <the second type annotation> to nodes which are ValueOf the node set.
    elif subscribed_class in (
            TypeshedClass('_typeshed', 'SupportsKeysAndGetItem'),
            TypeshedClass('_typeshed', 'SupportsItems'),
            TypeshedClass('typing', 'Mapping'),
            TypeshedClass('typing', 'MutableMapping'),
            TypeshedClass('types', 'MappingProxyType'),
            TypeshedClass('builtins', 'dict'),
            TypeshedClass('collections', 'ChainMap'),
            TypeshedClass('collections', 'defaultdict'),
            TypeshedClass('collections', 'OrderedDict')
    ):
        return [{(RelationType.IterTargetOf, None), (RelationType.KeyOf, None)},
                {(RelationType.ValueOf, None)}]
    # Counter-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf, KeyOf the node set.
    elif subscribed_class == TypeshedClass('collections', 'Counter'):
        return [{(RelationType.IterTargetOf, None), (RelationType.KeyOf, None)}]
    # Awaitable-like
    # Ascribe <the first type annotation> to nodes which are YieldFromAwaitResultOf the node set.
    elif subscribed_class == TypeshedClass('typing', 'Awaitable'):
        return [{(RelationType.YieldFromAwaitResultOf, None)}]
    # Generator-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf the node set.
    # Ascribe <the second type annotation> to nodes which are SendTargetOf the node set.
    # Ascribe <the third type annotation> to nodes which are YieldFromAwaitResultOf the node set.
    elif subscribed_class in (
            TypeshedClass('typing', 'Generator'),
            TypeshedClass('typing', 'Coroutine')
    ):
        return [{(RelationType.IterTargetOf, None)}, {(RelationType.SendTargetOf, None)},
                {(RelationType.YieldFromAwaitResultOf, None)}]
    # AsyncGenerator-like
    # Ascribe <the first type annotation> to nodes which are IterTargetOf the node set.
    # Ascribe <the second type annotation> to nodes which are SendTargetOf the node set.
    elif subscribed_class == TypeshedClass('typing', 'AsyncGenerator'):
        return [{(RelationType.IterTargetOf, None)}, {(RelationType.SendTargetOf, None)}]
    # tuple-like
    # Ascribe <the i-th type annotation> to nodes which are ElementOf i the node set.
    elif subscribed_class == TypeshedClass('builtins', 'tuple'):
        return [{(RelationType.ElementOf, i)} for i in range(number_of_type_parameters)]
    # Callable-like
    # Ascribe <the i-th type annotation> to nodes which are ParameterOf i the node set.
    # Ascribe <the last type annotation> to nodes which are ReturnValueOf the node set.
    elif subscribed_class in (
            TypeshedClass('typing', 'Callable'),
            TypeshedClass('builtins', 'staticmethod'),
            TypeshedClass('builtins', 'classmethod')
    ):
        if number_of_type_parameters:
            return [{(RelationType.ParameterOf, i)} for i in range(number_of_type_parameters - 1)] + [
                {(RelationType.ReturnValueOf, None)}]
        else:
            return []
    else:
        logging.error('Unknown semantics of subscribed class %s!', subscribed_class)
        return []
