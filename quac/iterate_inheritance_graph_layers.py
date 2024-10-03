import collections
import typing

import networkx as nx

from type_definitions import RuntimeClass


def yield_all_derived_base_pairs(derived: RuntimeClass, seen: typing.AbstractSet[RuntimeClass]=frozenset()):
    if derived not in seen:
        new_seen = seen | frozenset([derived])
        for base in derived.__bases__:
            yield (derived, base)
            yield from yield_all_derived_base_pairs(base, new_seen)


def construct_base_to_derived_graph(runtime_class_set: typing.AbstractSet[RuntimeClass]) -> nx.DiGraph:
    base_to_derived_graph: nx.DiGraph = nx.DiGraph()

    for runtime_class in runtime_class_set:
        for derived, base in yield_all_derived_base_pairs(runtime_class):
            base_to_derived_graph.add_edge(base, derived)

    return base_to_derived_graph


def breadth_first_search_layers(
        G: nx.DiGraph,
        starting_node_frozenset: typing.Optional[frozenset[typing.Any]] = None
) -> typing.Iterator[set[typing.Any]]:
    if starting_node_frozenset is None:
        starting_node_set = {
            node
            for node, in_degree in G.in_degree
            if not in_degree
        }
    else:
        starting_node_set = set(starting_node_frozenset)

    visited: set[typing.Any] = starting_node_set.copy()
    current_layer: set[typing.Any] = starting_node_set.copy()

    while current_layer:
        yield current_layer

        # Get the next layer of nodes
        next_layer: set[typing.Any] = set()
        for node in current_layer:
            if node in G.nodes:
                for succ in G.successors(node):
                    if succ not in visited:
                        visited.add(succ)
                        next_layer.add(succ)

        current_layer = next_layer


def iterate_inheritance_graph_layers(runtime_class_set: typing.AbstractSet[RuntimeClass]):
    base_to_derived_graph = construct_base_to_derived_graph(runtime_class_set)
    yield from breadth_first_search_layers(base_to_derived_graph)
