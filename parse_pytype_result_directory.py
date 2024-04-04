import argparse
import ast
import builtins
import importlib
import json
import logging
import os
import os.path
import sys
import typing

from collections import defaultdict

from query_result_dict import QueryDict, RawResultDefaultdict, RawResultDict, raw_result_dict_from_query_dict_and_raw_result_defaultdict
from type_annotation_to_string import type_annotation_to_string


# pytype_pyi_directory_path: '/tmp/.pytype/pyi/'
# module_name: 'demo.test_inbox'
# return: '/tmp/.pytype/pyi/demo/test_inbox.pyi'
def pyi_file_path_from_pytype_pyi_directory_path_and_module_name(
    pytype_pyi_directory_path: str,
    module_name: str
) -> str:
    module_name_components = module_name.split('.')
    python_file_relpath_without_ext: str = os.path.sep.join(module_name_components)
    return os.path.join(pytype_pyi_directory_path, python_file_relpath_without_ext + '.pyi')


class ASTNameVisitor(ast.NodeVisitor):
    def __init__(self):
        self.ast_name_id_to_ast_name_list_dict: defaultdict[
            str,
            list[ast.Name]
        ] = defaultdict(list)

    def visit_Name(self, ast_name: ast.Name):
        self.ast_name_id_to_ast_name_list_dict[ast_name.id].append(ast_name)


def generate_module_names_and_pyi_file_paths(query_dict, pytype_pyi_directory):
    for module_name, module_level_query_dict in query_dict.items():
        pyi_file_path = pyi_file_path_from_pytype_pyi_directory_path_and_module_name(pytype_pyi_directory, module_name)
        if os.path.isfile(pyi_file_path):
            yield module_name, pyi_file_path


def get_top_level_ancestor_node(ast_module: ast.Module, child_to_parent_dict: dict[ast.AST, ast.AST], node: ast.AST) -> ast.AST:
    ancestor_node = node
    while child_to_parent_dict[ancestor_node] is not ast_module:
        ancestor_node = child_to_parent_dict[ancestor_node]
    return ancestor_node


def parse(
    query_dict: QueryDict,
    module_search_path: str,
    pytype_pyi_directory_path: str
) -> RawResultDict:
    raw_result_defaultdict: RawResultDefaultdict = defaultdict(lambda: defaultdict(lambda: defaultdict(lambda: defaultdict(list))))

    sys.path.insert(0, module_search_path)

    for module_name, pyi_file_path in generate_module_names_and_pyi_file_paths(query_dict, pytype_pyi_directory_path):
        logging.info('Handling module `%s` with .pyi file `%s`', module_name, pyi_file_path)

        module = importlib.import_module(module_name)
        logging.info('Successfully imported module `%s`', module_name)

        with open(pyi_file_path, 'r') as fp:
            code: str = fp.read()
            ast_module: ast.Module = ast.parse(code)

            class_name_or_global_to_function_name_to_return_type_annotation_node: defaultdict[
                str, # class_name_or_global
                defaultdict[
                    str, # function_name
                    ast.AST # type_annotation
                ]
            ] = defaultdict(lambda: defaultdict())

            for node in ast_module.body:
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name in module.__dict__:
                    if node.returns is not None:
                        class_name_or_global_to_function_name_to_return_type_annotation_node['global'][node.name] = node.returns
                elif isinstance(node, ast.ClassDef) and node.name in module.__dict__:
                    for child_node in node.body:
                        if isinstance(child_node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            if child_node.returns is not None:
                                class_name_or_global_to_function_name_to_return_type_annotation_node[node.name][child_node.name] = child_node.returns
            
            logging.info('Successfully extracted return type annotation nodes from .pyi file `%s`', pyi_file_path)

            exec_globals = dict()
            exec_globals.update(builtins.__dict__)
            exec_globals.update(typing.__dict__)
            exec_globals.update(module.__dict__)

            unknown_ast_name_id_set: set[str] = set()

            for class_name_or_global, function_name_to_type_annotation in class_name_or_global_to_function_name_to_return_type_annotation_node.items():
                for function_name, type_annotation in function_name_to_type_annotation.items():
                    for node in ast.walk(type_annotation):
                        if isinstance(node, ast.Name) and node.id not in exec_globals:
                            unknown_ast_name_id_set.add(node.id)
            
            logging.info('Unknown ast.Name ids in return type annotation nodes: %s', json.dumps(list(unknown_ast_name_id_set)))
            
            ast_name_visitor = ASTNameVisitor()
            ast_name_visitor.visit(ast_module)

            child_to_parent_dict: dict[ast.AST, ast.AST] = dict()
            for parent in ast.walk(ast_module):
                for child in ast.iter_child_nodes(parent):
                    child_to_parent_dict[child] = parent

            for unknown_ast_name_id in unknown_ast_name_id_set:
                logging.info('Trying to resolve unknown ast.Name id `%s`', unknown_ast_name_id)
                first_ast_name_with_unknown_ast_name_id: ast.Name = ast_name_visitor.ast_name_id_to_ast_name_list_dict[unknown_ast_name_id][0]

                top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id: ast.AST = get_top_level_ancestor_node(
                    ast_module,
                    child_to_parent_dict,
                    first_ast_name_with_unknown_ast_name_id
                )

                ast_unparse_top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id: str = ast.unparse(
                    top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id
                )

                logging.info('Top-level ancestor node of ast.Name with unknown ast.Name id: `%s`', ast_unparse_top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id)

                exec(ast_unparse_top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id, exec_globals)

                logging.info('Successfully executed `%s`', ast_unparse_top_level_ancestor_node_of_first_ast_name_with_unknown_ast_name_id)
        
            for class_name_or_global, function_name_to_return_type_annotation_node in class_name_or_global_to_function_name_to_return_type_annotation_node.items():
                for function_name, return_type_annotation_node in function_name_to_return_type_annotation_node.items():
                    ast_unparse_return_type_annotation_node: str = ast.unparse(return_type_annotation_node)
                    return_type_annotation = eval(ast_unparse_return_type_annotation_node, exec_globals)

                    return_type_annotation_string: str = type_annotation_to_string(return_type_annotation)

                    raw_result_defaultdict[module_name][class_name_or_global][function_name]['return'].append(return_type_annotation_string)
                    logging.info('Successfully recovered return type annotation for %s %s: %s', class_name_or_global, function_name, return_type_annotation_string)

    sys.path.pop(0)

    return raw_result_dict_from_query_dict_and_raw_result_defaultdict(query_dict, raw_result_defaultdict)


if __name__ == '__main__':
    # set up logging
    FORMAT = '%(asctime)s %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.INFO)

    parser = argparse.ArgumentParser()
    parser.add_argument('-q', '--query-dict', type=str, required=True, help='Query dict JSON file, e.g. {"src.meerkat.configurations.infrastructure.rest.health.registry": {"HealthService": {"boot": ["container"]}}, "src.meerkat.data_providers.database.mongo.transformers": {"PostDocumentTransformer": {"transform_to_domain_object": ["return"]}}, "src.meerkat.domain.post.value_objects.id": {"Id": {"__init__": ["value"]}}, "src.meerkat.entrypoints.rest.post.registry": {"PostService": {"boot": ["container"]}}}')
    parser.add_argument('-m', '--module-search-path', type=str, required=True, help='Module search path, e.g. /tmp/module_search_path')
    parser.add_argument('-p', '--pytype-pyi-directory', type=str, required=True, help='Pytype .pyi directory, e.g. /tmp/.pytype/pyi')
    args = parser.parse_args()

    with open(args.query_dict, 'r') as fp:
        query_dict = json.load(fp)

    result_dict = parse(query_dict, args.module_search_path, args.pytype_pyi_directory)

    json.dump(result_dict, sys.stdout)
