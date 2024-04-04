import builtins
import logging

from typing import Callable

import lark

from lark import Lark, Token, Tree

from static_import_analysis import do_static_import_analysis

from type_inference_result import TypeInferenceResult, TypeInferenceClass

builtin_class_names: set[str] = {k for k, v in builtins.__dict__.items() if isinstance(v, type)}

parser: Lark = Lark(r"""
type_annotation: class | subscription | none | ellipsis
class: NAME ("." NAME)* | "'" NAME ("." NAME)* "'" | "\"" NAME ("." NAME)* "\""
subscription: class "[" subscription_list_element ("," subscription_list_element)*"]"
subscription_list_element: type_annotation | 
none: "None"
ellipsis: "..."

%import common.WS
%import python.NAME

%ignore WS
""",
start='type_annotation',
parser='lalr')


def parser_parse(
    type_annotation_string: str
) -> Tree:
    global parser
    return parser.parse(
        # Replace all occurrences of '_@_' with '.'
        type_annotation_string.replace('_@_', '.')
    )


def handle_type_annotation_tree(
        type_annotation_tree: Tree,
        name_to_defined_or_imported_class_dict: dict[str, TypeInferenceClass]
) -> TypeInferenceResult:
    # type_annotation: class | subscription
    class_or_subscription_tree: Tree = type_annotation_tree.children[0]
    rule: str = class_or_subscription_tree.data.value
    if rule == 'class':
        type_inference_class: TypeInferenceClass = handle_class_tree(
            class_or_subscription_tree,
            name_to_defined_or_imported_class_dict
        )
        return TypeInferenceResult(type_inference_class)
    elif rule == 'subscription':
        return handle_subscription_tree(
            class_or_subscription_tree,
            name_to_defined_or_imported_class_dict
        )
    elif rule == 'none':
        return TypeInferenceResult(TypeInferenceClass('builtins', 'NoneType'))
    elif rule == 'ellipsis':
        return TypeInferenceResult(TypeInferenceClass('builtins', 'Ellipsis'))
    else:
        assert False


def handle_class_tree(
        class_tree: Tree,
        name_to_defined_or_imported_class_dict: dict[str, TypeInferenceClass]
) -> TypeInferenceClass:
    # class: NAME ("." NAME)*
    names: list[str] = [child.value for child in class_tree.children]
    if len(names) == 1:
        name: str = names[0]
        # Resolve built-in classes
        if name in builtin_class_names:
            return TypeInferenceClass('builtins', name)
        # Resolve defined or imported class
        elif name in name_to_defined_or_imported_class_dict:
            return name_to_defined_or_imported_class_dict[name]
        # Leave name as is, most likely a halluciation
        else:
            logging.error('Cannot resolve name %s. Leaving the name as is.', name)
            return TypeInferenceClass(None, name)
    elif len(names) > 1:
        module_name: str = '.'.join(names[:-1])
        class_name: str = names[-1]
        return TypeInferenceClass(module_name, class_name)
    else:
        assert False


def handle_subscription_tree(
        subscription_tree: Tree,
        name_to_defined_or_imported_class_dict: dict[str, TypeInferenceClass]
) -> TypeInferenceResult:
    # subscription: class "[" subscription_list_element ("," subscription_list_element)*"]"
    class_tree: Tree = subscription_tree.children[0]
    type_inference_class: TypeInferenceClass = handle_class_tree(
        class_tree,
        name_to_defined_or_imported_class_dict
    )
    filled_type_variable_list: list[TypeInferenceResult] = [
        handle_subscription_list_element(
            subscription_list_element_tree,
            name_to_defined_or_imported_class_dict
        )
        for subscription_list_element_tree in subscription_tree.children[1:]
    ]
    # Special handling for `builtins.tuple`'s with 1 filled type variable
    if type_inference_class == TypeInferenceClass('builtins', 'tuple') and len(filled_type_variable_list) == 1:
        filled_type_variable_list.append(TypeInferenceResult(TypeInferenceClass('builtins', 'ellipsis')))
    # Special handling for `typing.Generator`'s with 1 filled type variable
    if type_inference_class == TypeInferenceClass('typing', 'Generator') and len(filled_type_variable_list) == 1:
        filled_type_variable_list.append(TypeInferenceResult(TypeInferenceClass('builtins', 'None')))
        filled_type_variable_list.append(TypeInferenceResult(TypeInferenceClass('builtins', 'None')))
    return TypeInferenceResult(type_inference_class, tuple(filled_type_variable_list))


def handle_subscription_list_element(
        subscription_list_element_tree: Tree,
        name_to_defined_or_imported_class_dict: dict[str, TypeInferenceClass]
) -> TypeInferenceResult:
    # subscription_list_element: type_annotation |
    if subscription_list_element_tree.children:
        type_annotation_tree: Tree = subscription_list_element_tree.children[0]
        return handle_type_annotation_tree(
            type_annotation_tree,
            name_to_defined_or_imported_class_dict
        )
    else:
        # fix for empty `subscription_list_element`'s
        return TypeInferenceResult(TypeInferenceClass('typing', 'Any'))


def get_type_annotation_parser(
    module_name_to_class_name_to_method_name_to_parameter_name_list_dict: dict[str, dict[str, dict[str, list[str]]]],
    module_name_to_import_from_tuple_set_dict: dict[str, set[tuple[str, str, str]]]
) -> Callable[[str, str], TypeInferenceResult]:
    # Construct module_name_to_name_to_defined_or_imported_class_dict
    module_name_to_name_to_defined_or_imported_class_dict: dict[
        str,
        dict[str, TypeInferenceClass]
    ] = dict()
    
    module_names: set[str] = module_name_to_class_name_to_method_name_to_parameter_name_list_dict.keys() | module_name_to_import_from_tuple_set_dict.keys()
    
    for module_name in module_names:
        name_to_defined_or_imported_class_dict = dict()

        for (
            module_name_,
            imported_name,
            imported_name_alias
        ) in module_name_to_import_from_tuple_set_dict[module_name]:
            name_to_defined_or_imported_class_dict[
                imported_name_alias
            ] = TypeInferenceClass(module_name_, imported_name)

        for class_name in module_name_to_class_name_to_method_name_to_parameter_name_list_dict[module_name]:
            name_to_defined_or_imported_class_dict[
                class_name
            ] = TypeInferenceClass(module_name, class_name)

        module_name_to_name_to_defined_or_imported_class_dict[
            module_name
        ] = name_to_defined_or_imported_class_dict

    # Define type_annotation_parser
    def type_annotation_parser(
            module_name: str,
            type_annotation_string: str
    ) -> TypeInferenceResult:
        nonlocal module_name_to_name_to_defined_or_imported_class_dict

        name_to_defined_or_imported_class_dict = module_name_to_name_to_defined_or_imported_class_dict.get(
            module_name,
            dict()
        )

        try:
            type_annotation_tree: Tree = parser_parse(type_annotation_string)

            return handle_type_annotation_tree(
                type_annotation_tree,
                name_to_defined_or_imported_class_dict
            )
        except lark.exceptions.LarkError:
            import pudb
            pudb.set_trace()
            
            logging.error('Cannot resolve type annotation %s. Leaving the type annotation as is.', type_annotation_string)
            
            return TypeInferenceResult(TypeInferenceClass(None, type_annotation_string))


    # Return type_annotation_parser
    return type_annotation_parser
