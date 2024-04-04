import argparse
import ast
import difflib
import json
import logging
import os
import os.path
import pdb
import sys

from collections import defaultdict, OrderedDict

from lark import Lark, Token, Tree
from ordered_set import OrderedSet

from get_parameter_name_list_from_ast_function_def import get_parameter_name_list_from_ast_function_def
from python_file_path_from_module_search_path_and_module_name import python_file_path_from_module_search_path_and_module_name
from query_result_dict import QueryDict, RawResultDefaultdict, RawResultDict, raw_result_dict_from_query_dict_and_raw_result_defaultdict

result_file_parser: Lark = Lark(r"""
result_file: (function_type_inference_result)*
function_type_inference_result: NAME (parameter_or_return_value_type_inference_results)+
parameter_or_return_value_type_inference_results: "[" type_annotation ("," type_annotation)* "]"
type_annotation: STRING

%import common.WS
%import python.NAME
%import python.STRING

%ignore WS
""",
start='result_file',
parser='lalr')


def extract_type_annotation_string(type_annotation_tree: Tree) -> str:
    type_annotation: str = type_annotation_tree.children[0].value
    return eval(type_annotation)


def extract_recursive_type_annotation_string(recursive_type_annotation_tree: Tree) -> str:
    components: list[str] = []

    class_name_string: str = extract_class_name_string(recursive_type_annotation_tree.children[0])
    components.append(class_name_string)
    
    if isinstance(
        recursive_type_annotation_tree.children[-1],
        Tree
    ) and recursive_type_annotation_tree.children[-1].data.value == 'type_annotation_list':
        type_annotation_list_tree: Tree = recursive_type_annotation_tree.children[-1]
        components_in_type_annotation_list: list[str] = []

        for recursive_type_annotation_tree_in_type_annotation_list in type_annotation_list_tree.children:
            components_in_type_annotation_list.append(
                extract_recursive_type_annotation_string(recursive_type_annotation_tree_in_type_annotation_list)
            )
        
        components.append('[')
        components.append(','.join(components_in_type_annotation_list))
        components.append(']')
    
    return ''.join(components)


def extract_class_name_string(class_name_tree: Tree) -> str:
    return '.'.join((
        name.value
        for name in class_name_tree.children
    ))


def parse(
    query_dict: QueryDict,
    stray_module_search_absolute_path: str,
    stray_result_directory_path: str,
    module_search_path: str | None = None
) -> RawResultDict:
    global result_file_parser

    if module_search_path is None:
        module_search_path = stray_module_search_absolute_path

    prelimary_result_dict: RawResultDefaultdict = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: defaultdict(list))))

    for module_name, module_level_query_dict in query_dict.items():
        python_file_absolute_path: str = python_file_path_from_module_search_path_and_module_name(
            module_search_path,
            module_name
        )

        # stray_python_file_absolute_path: '/tmp/module_search_path/src/meerkat/entrypoints/rest/post/registry.py'
        stray_python_file_absolute_path: str = python_file_path_from_module_search_path_and_module_name(
            stray_module_search_absolute_path,
            module_name
        )

        # result_file_name: '-tmp-module_search_path-src-meerkat-entrypoints-rest-post-registry.py_orderred_'
        result_file_name: str = f"{stray_python_file_absolute_path.replace('/', '-')}_orderred_"

        # result_file_path: '/root/Stray/result/-tmp-module_search_path-src-meerkat-entrypoints-rest-post-registry.py_orderred_'
        result_file_path: str = os.path.join(
            stray_result_directory_path,
            result_file_name
        )

        if os.path.exists(python_file_absolute_path) and os.path.exists(result_file_path):
            logging.info('Result file `%s` matches Python file `%s`', result_file_path, python_file_absolute_path)

            # TODO: structured type annotations
            # extract a prelimiary structured representation of the type inference results within the result file 
            # function_name_and_list_of_list_of_type_annotation_string_list: [('__init__', [['meerkat.domain.post.value_objects.id.Id'], ['uuid.UUID'], ['None']]), ('is_valid', [['meerkat.domain.post.value_objects.id.Id'], ['builtins.bool']]), ('__str__', [['meerkat.domain.post.value_objects.id.Id'], ['builtins.str']])]
            # note that there is no class_name for each function_name
            # but we assume that the function_name's are in increasing lineno order
            # and we associate them with (class_name, function_name, lineno) tuples parsed from the file
            fp = open(result_file_path, 'r')
            result_file_path_contents: str = fp.read()
            fp.close()

            result_file_parse_tree: Tree = result_file_parser.parse(result_file_path_contents)

            function_name_and_type_annotation_string_set_list_list: list[
                tuple[
                    str, # function_name
                    list[
                        OrderedSet[
                            str # type_annotation_string
                        ]
                    ]
                ]
            ] = []
            
            for function_type_inference_result_tree in result_file_parse_tree.find_data('function_type_inference_result'):
                function_name_token: Token = function_type_inference_result_tree.children[0]
                function_name: str = function_name_token.value

                type_annotation_string_set_list: list[
                    OrderedSet[
                        str # type_annotation_string
                    ]
                ] = []

                for parameter_or_return_value_type_inference_results_tree in function_type_inference_result_tree.find_data('parameter_or_return_value_type_inference_results'):
                    type_annotation_string_set: OrderedSet[
                        str # type_annotation_string
                    ] = OrderedSet()


                    for type_annotation_tree in parameter_or_return_value_type_inference_results_tree.find_data('type_annotation'):
                        type_annotation_string: str = extract_type_annotation_string(type_annotation_tree)

                        type_annotation_string_set.add(type_annotation_string)


                    type_annotation_string_set_list.append(type_annotation_string_set)
                
                function_name_and_type_annotation_string_set_list_list.append(
                    (
                        function_name,
                        type_annotation_string_set_list
                    )
                )

            # extract a structured representation of functions in Python file
            # class_name_function_name_and_lineno_list: [('Id', '__init__', 6), ('Id', 'is_valid', 9), ('Id', '__str__', 12)]
            fp = open(python_file_absolute_path, 'r')
            code: str = fp.read()
            fp.close()

            module: ast.Module = ast.parse(code)

            class_name_function_name_and_parameter_name_list_list: list[tuple[str, str, list[str]]] = []

            for node in module.body:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    class_name_function_name_and_parameter_name_list_list.append(('global', node.name, get_parameter_name_list_from_ast_function_def(node)))
                elif isinstance(node, ast.ClassDef):
                    for child_node in node.body:
                        if isinstance(child_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            class_name_function_name_and_parameter_name_list_list.append((node.name, child_node.name, get_parameter_name_list_from_ast_function_def(child_node)))
            

            # match each function_name in function_name_and_type_annotation_string_set_list_list
            # to a function_name in class_name_function_name_and_parameter_name_list_list
            # a: ['__init__', 'is_valid', '__str__']
            # b: ['__init__', 'is_valid', '__str__']
            a: list[str] = [ function_name for function_name, _ in function_name_and_type_annotation_string_set_list_list ]
            b: list[str] = [ function_name for class_name, function_name, parameter_name_list in class_name_function_name_and_parameter_name_list_list ]

            sequence_matcher: difflib.SequenceMatcher = difflib.SequenceMatcher(None, a, b)
            # match: Match(a=0, b=0, size=3)
            for match in sequence_matcher.get_matching_blocks():
                a_index: int = match.a
                b_index: int = match.b
                size: int = match.size
                for offset in range(size):
                    class_name, function_name, parameter_name_list = class_name_function_name_and_parameter_name_list_list[b_index + offset]
                    _, type_annotation_string_set_list = function_name_and_type_annotation_string_set_list_list[a_index + offset]

                    logging.info('Matching function %s in result file `%s` with module %s, class %s, function %s', function_name, result_file_path, module_name, class_name, function_name)

                    for parameter_name, type_annotation_string_set in zip(parameter_name_list, type_annotation_string_set_list[:-1]):
                        prelimary_result_dict[module_name][class_name][function_name][parameter_name].extend(type_annotation_string_set)
                    
                    parameter_name = 'return'
                    type_annotation_string_set = type_annotation_string_set_list[-1]
                    prelimary_result_dict[module_name][class_name][function_name][parameter_name].extend(type_annotation_string_set)
        else:
            logging.info('Cannot find result file that matches Python file `%s`', python_file_absolute_path)
        
    return raw_result_dict_from_query_dict_and_raw_result_defaultdict(query_dict, prelimary_result_dict)


if __name__ == '__main__':
    # set up logging
    FORMAT = '%(asctime)s %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.INFO)

    parser = argparse.ArgumentParser()
    parser.add_argument('-q', '--query-dict', type=str, required=True, help='Query dict JSON file, e.g. {"src.meerkat.configurations.infrastructure.rest.health.registry": {"HealthService": {"boot": ["container"]}}, "src.meerkat.data_providers.database.mongo.transformers": {"PostDocumentTransformer": {"transform_to_domain_object": ["return"]}}, "src.meerkat.domain.post.value_objects.id": {"Id": {"__init__": ["value"]}}, "src.meerkat.entrypoints.rest.post.registry": {"PostService": {"boot": ["container"]}}}')
    parser.add_argument('-s', '--absolute-module-search-path', type=str, required=True, help='Absolute module search path, e.g. /tmp/module_search_path')
    parser.add_argument('-r', '--stray-result-directory', type=str, required=True, help='Stray result directory, e.g. stray/result')
    parser.add_argument('-o', '--output-file', type=str, required=True, help='Output JSON file')

    args = parser.parse_args()

    with open(args.query_dict, 'r') as fp:
        query_dict = json.load(fp)

    result_dict = parse(query_dict, args.absolute_module_search_path, args.stray_result_directory)

    with open(args.output_file, 'w') as fp:
        json.dump(result_dict, fp, indent=4)
