import typing
from typing import Generator

from lark import Lark, Token, Tree


class TypeInferenceClass:
    __slots__ = ('module_name', 'class_name')

    def __init__(self, module_name: str | None, name: str):
        self.module_name = module_name
        self.class_name = name

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeInferenceClass):
            return self.module_name == other.module_name and self.class_name == other.class_name
        return False

    def __hash__(self) -> int:
        return hash((self.module_name, self.class_name))

    def __repr__(self) -> str:
        # Special representations for builtins.NoneType and builtins.ellipsis
        if self.module_name == 'builtins':
            if self.class_name == 'NoneType':
                return 'None'
            elif self.class_name == 'ellipsis':
                return '...'

        if self.module_name is not None:
            return f'{self.module_name}.{self.class_name}'
        else:
            return self.class_name


class TypeInferenceResult:
    __slots__ = ('type_inference_class', 'filled_type_variables')

    def __init__(self, type_inference_class: TypeInferenceClass, filled_type_variables: tuple['TypeInferenceResult', ...] = ()):
        self.type_inference_class = type_inference_class
        self.filled_type_variables = filled_type_variables

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeInferenceResult):
            return (
                self.type_inference_class == other.type_inference_class
                and self.filled_type_variables == other.filled_type_variables
            )
        return False

    def __hash__(self) -> int:
        return hash((self.type_inference_class, self.filled_type_variables))

    def __repr__(self) -> str:
        components: list[str] = [str(self.type_inference_class)]

        if self.filled_type_variables:
            filled_type_variable_components: list[str] = [
                str(filled_type_variable)
                for filled_type_variable in self.filled_type_variables
            ]

            components.append('[')

            # Special handling for typing.Callable and collections.abc.Callable
            if self.type_inference_class in (
                TypeInferenceClass('typing', 'Callable'),
                TypeInferenceClass('collections.abc', 'Callable')
            ):
                # Situation 1: len(filled_type_variable_components) == 1
                # Add '[]' representing empty parameter list in addition to filled_type_variable_components[0]
                if len(filled_type_variable_components) == 1:
                    components.append('[]')
                    components.append(', ')
                    components.append(filled_type_variable_components[0])
                # Situation 2: len(filled_type_variable_components) == 2 and self.filled_type_variables[0].type_inference_class == TypeInferenceClass('builtins', 'ellipsis')
                # Directly extend with filled_type_variable_components
                elif len(filled_type_variable_components) == 2 and self.filled_type_variables[0].type_inference_class == TypeInferenceClass('builtins', 'ellipsis'):
                    components.append(', '.join(filled_type_variable_components))
                # Situation 3: Other situations where len(filled_type_variable_components) > 1
                # Add '[' and ']' at the start and end of the parameter list
                elif len(filled_type_variable_components) > 1:
                    components.append('[')
                    components.append(', '.join(filled_type_variable_components[:-1]))
                    components.append(']')
                    components.append(', ')
                    components.append(filled_type_variable_components[-1])
            else:
                components.append(', '.join(filled_type_variable_components))
            
            components.append(']')

        return ''.join(components)


def iterate_type_inference_classes(type_inference_result: TypeInferenceResult) -> Generator[
    TypeInferenceClass,
    None,
    None
]:
    yield type_inference_result.type_inference_class
    for filled_type_variable in type_inference_result.filled_type_variables:
        yield from iterate_type_inference_classes(filled_type_variable)


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
