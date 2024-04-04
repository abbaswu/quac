"""
To generate an HTML coverage report for disjoint_set.py under test:

- Run Coverage: coverage run --source=disjoint_set test_disjoint_set.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""

from disjoint_set import DisjointSet


if __name__ == '__main__':
    ds = DisjointSet()
    assert ds.find(1) == 1

    def get_merge_callback_with_assertion(expected_target_set_top_element, expected_acquirer_set_top_element):
        def merge_callback_with_assertion(
            target_set_top_element,
            target_set,
            acquirer_set_top_element,
            acquirer_set
        ):
            assert target_set_top_element == expected_target_set_top_element and acquirer_set_top_element == expected_acquirer_set_top_element
        return merge_callback_with_assertion

    ds.union(1, 2, get_merge_callback_with_assertion(1, 2))
    assert ds.find(1) == 2
    assert ds.find(2) == 2
    assert ds.connected(1, 2)
    assert not ds.connected(1, 3)
    assert not "a" in ds
    assert ds.find("a") == 'a'
    assert list(ds) == [(1, 2), (2, 2), (3, 3), ('a', 'a')]
    assert list(ds.itersets()) == [(2, {1, 2}), (3, {3}), ('a', {'a'})]
