"""
Set-trie container of sets for efficient supersets/subsets of a set over a set of sets queries.
Adapted from https://github.com/mmihaltz/pysettrie
"""
from typing import TypeVar, Iterable, Iterator, AbstractSet, Optional, Sequence

from trie import TrieNode, search_or_create, search

# Define a type variable
K = TypeVar('K')
V = TypeVar('V')


SetTrieNode = TrieNode[K, bool]


def add(root: SetTrieNode[K], character_set: AbstractSet[K]) -> None:
    """Add a set to the set-trie."""
    sorted_character_sequence: list[K] = sorted(character_set)
    added_node: SetTrieNode[K] = search_or_create(root, sorted_character_sequence)
    added_node.value = True


def contains(root: SetTrieNode[K], character_set: AbstractSet[K]) -> bool:
    """Check if a set is in the set-trie."""
    sorted_character_sequence: list[K] = sorted(character_set)
    node: Optional[SetTrieNode[K]] = search(root, sorted_character_sequence)
    return node is not None and node.value is not None


def iterate_immediate_supersets_containing_sorted_character_sequence(
        root: SetTrieNode[K],
        sorted_character_sequence: Sequence[K],
        current_set: frozenset[K] = frozenset(),
        extra_character_set: frozenset[K] = frozenset()
) -> Iterator[frozenset[K]]:
    # we still have elements to find
    if sorted_character_sequence:
        first_character, remaining_sorted_character_sequence = sorted_character_sequence[0], sorted_character_sequence[1:]
        for character, child in root.children.items():
            # don't go to subtrees where current element cannot be
            if character < first_character:
                yield from iterate_immediate_supersets_containing_sorted_character_sequence(
                    child,
                    sorted_character_sequence,
                    current_set | frozenset([character]),
                    extra_character_set | frozenset([first_character])
                )
            elif character == first_character:
                yield from iterate_immediate_supersets_containing_sorted_character_sequence(
                    child,
                    remaining_sorted_character_sequence,
                    current_set | frozenset([character]),
                    extra_character_set
                )
    # no more elements to find
    else:
        if root.value and extra_character_set:
            yield current_set
        else:
            for character, child in root.children.items():
                yield from iterate_immediate_supersets_containing_sorted_character_sequence(
                    child,
                    sorted_character_sequence,
                    current_set | frozenset([character]),
                    extra_character_set | frozenset([character])
                )


def iterate_immediate_supersets(root: SetTrieNode[K], character_set: AbstractSet[K]) -> Iterator[frozenset[K]]:
    yield from iterate_immediate_supersets_containing_sorted_character_sequence(
        root,
        sorted(character_set)
    )


def iterate_one_level_of_sets(
        root: SetTrieNode[K],
        current_set: frozenset[K] = frozenset()
) -> Iterator[frozenset[K]]:
    if root.value:
        yield current_set
    else:
        for character, child in root.children.items():
            yield from iterate_one_level_of_sets(
                child,
                current_set | frozenset([character])
            )


def create_set_trie(character_sets: Iterable[AbstractSet[K]]) -> SetTrieNode[K]:
    root: SetTrieNode[K] = TrieNode()
    for character_set in character_sets:
        add(root, character_set)
    return root
