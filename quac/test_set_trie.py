"""
To generate an HTML coverage report for set_trie.py under test:

- Run Coverage: coverage run --source=set_trie test_set_trie.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""

from set_trie import *


if __name__ == '__main__':
    root: SetTrieNode[int] = create_set_trie([{1, 3}, {1, 3, 5}, {1, 4}, {1, 2, 4}, {2, 4}, {2, 3, 5}])

    assert set(iterate_one_level_of_sets(root)) == {
        frozenset({1, 3}),
        frozenset({1, 4}),
        frozenset({1, 2, 4}),
        frozenset({2, 4}),
        frozenset({2, 3, 5})
    }

    assert set(iterate_immediate_supersets_containing_sorted_character_sequence(root, [1])) == {
        frozenset({1, 3}), frozenset({1, 4}), frozenset({1, 2, 4})
    }

    assert set(iterate_immediate_supersets_containing_sorted_character_sequence(root, [1, 3])) == {
        frozenset({1, 3, 5})
    }