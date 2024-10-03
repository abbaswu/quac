"""
To generate an HTML coverage report for set_trie.py under test:

- Run Coverage: coverage run --source=iterate_inheritance_graph_layers test_iterate_inheritance_graph_layers.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""
from get_types_in_module import get_types_in_module
from iterate_inheritance_graph_layers import iterate_inheritance_graph_layers


if __name__ == '__main__':
    from test_modules import multiple_inheritance

    types_in_module = get_types_in_module(multiple_inheritance)

    assert list(iterate_inheritance_graph_layers(types_in_module)) == [
        {object},
        {multiple_inheritance.A},
        {multiple_inheritance.B, multiple_inheritance.C},
        {multiple_inheritance.D}
    ]
