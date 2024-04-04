"""
User
Is there a Prefix Tree Map data structure where values can be indexed by keys which are lists of strings?
"""
import typing
from typing import TypeVar, Generic, Optional, Sequence

# Define a type variable
K = TypeVar('K')
V = TypeVar('V')


class TrieNode(Generic[K, V]):
    __slots__ = ('value', 'children')

    def __init__(self, value: Optional[V] = None):
        self.value: Optional[V] = value
        self.children: dict[K, TrieNode[K, V]] = {}


def search(root: TrieNode[K, V], character_sequence: Sequence[K]) -> typing.Optional[TrieNode[K, V]]:
    if not character_sequence:
        return root
    else:
        first_character, remaining_character_sequence = character_sequence[0], character_sequence[1:]
        if first_character not in root.children:
            return None
        else:
            return search(root.children[first_character], remaining_character_sequence)


def search_or_create(root: TrieNode[K, V], character_sequence: Sequence[K]) -> TrieNode[K, V]:
    if not character_sequence:
        return root
    else:
        first_character, remaining_character_sequence = character_sequence[0], character_sequence[1:]
        if first_character not in root.children:
            root.children[first_character] = TrieNode()
        return search_or_create(root.children[first_character], remaining_character_sequence)
