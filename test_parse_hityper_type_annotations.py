"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=parse_hityper_type_annotations test_parse_hityper_type_annotations.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""

from type_inference_result import TypeInferenceResult
from parse_hityper_type_annotations import parser_parse, handle_type_annotation_tree


def parse(
    type_annotation_string: str
) -> TypeInferenceResult:
    type_annotation_tree: Tree = parser_parse(type_annotation_string)
    
    return handle_type_annotation_tree(
        type_annotation_tree,
        dict()
    )


if __name__ == '__main__':
    assert str(parse('np_@_random_@_RandomState'))    
