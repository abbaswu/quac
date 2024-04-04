import typing

from lark import Lark, Token, Tree

from type_inference_result import TypeInferenceResult, TypeInferenceClass


parser: Lark = Lark(r"""
type_annotation: class | subscription
class: NAME ("." NAME)* | none | ellipsis
none: "None"
ellipsis: "..."
subscription: class filled_type_variable_list
filled_type_variable_list: "[" filled_type_variable_list_element? ("," filled_type_variable_list_element)* "]"
filled_type_variable_list_element: type_annotation | filled_type_variable_list

%import common.WS
%import python.NAME

%ignore WS
""",
start='type_annotation',
parser='lalr')


def handle_type_annotation_tree(
    type_annotation_tree: Tree
) -> TypeInferenceResult:
    # type_annotation: class | subscription
    class_or_subscription_tree: Tree = type_annotation_tree.children[0]
    rule: str = class_or_subscription_tree.data.value
    if rule == 'class':
        type_inference_class: TypeInferenceClass = handle_class_tree(
            class_or_subscription_tree
        )
        return TypeInferenceResult(type_inference_class)
    elif rule == 'subscription':
        return handle_subscription_tree(
            class_or_subscription_tree
        )
    else:
        assert False


def handle_class_tree(
    class_tree: Tree
) -> TypeInferenceClass:
    # class: NAME ("." NAME)* | none | ellipsis
    first_child: Token | Tree  = class_tree.children[0]

    if isinstance(first_child, Token):
        names: list[str] = [ child.value for child in class_tree.children ]
        module_name: str = '.'.join(names[:-1])
        class_name: str = names[-1]
        return TypeInferenceClass(module_name, class_name)
    else:
        rule: str = first_child.data.value
        if rule == 'none':
            return TypeInferenceClass('builtins', 'NoneType')
        elif rule == 'ellipsis':
            return TypeInferenceClass('builtins', 'ellipsis')


def handle_subscription_tree(
    subscription_tree: Tree
) -> TypeInferenceResult:
    # subscription: class filled_type_variable_list
    class_tree: Tree = subscription_tree.children[0]
    type_inference_class: TypeInferenceClass = handle_class_tree(
        class_tree
    )
    filled_type_variable_list_tree: Tree = subscription_tree.children[1]
    filled_type_variable_list: tuple[TypeInferenceResult, ...] = tuple(handle_filled_type_variable_list_tree(
        filled_type_variable_list_tree
    ))

    return TypeInferenceResult(type_inference_class, filled_type_variable_list)


def handle_filled_type_variable_list_tree(
    filled_type_variable_list_tree: Tree
) -> typing.Generator[
    TypeInferenceResult,
    None,
    None
]:
    # filled_type_variable_list: "[" filled_type_variable_list_element? ("," filled_type_variable_list_element)* "]"
    filled_type_variable_list_element_tree_list: list[Tree] = filled_type_variable_list_tree.children
    if len(filled_type_variable_list_element_tree_list) == 0:
        return
    else:
        for filled_type_variable_list_element_tree in filled_type_variable_list_element_tree_list:
            yield from handle_filled_type_variable_list_element_tree(
                filled_type_variable_list_element_tree
            )


def handle_filled_type_variable_list_element_tree(
    filled_type_variable_list_element_tree: Tree
) -> typing.Generator[
    TypeInferenceResult,
    None,
    None
]:
    # filled_type_variable_list_element: type_annotation | filled_type_variable_list
    type_annotation_or_filled_type_variable_list_tree = filled_type_variable_list_element_tree.children[0]
    rule: str = type_annotation_or_filled_type_variable_list_tree.data.value
    if rule == 'type_annotation':
        yield handle_type_annotation_tree(
            type_annotation_or_filled_type_variable_list_tree
        )
    elif rule == 'filled_type_variable_list':
        yield from handle_filled_type_variable_list_tree(
            type_annotation_or_filled_type_variable_list_tree
        )


def parse(
    type_annotation_string: str
) -> TypeInferenceResult:
    type_annotation_tree: Tree = parser.parse(type_annotation_string)
    return handle_type_annotation_tree(type_annotation_tree)
