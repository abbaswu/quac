"""
Nodes that access names:

- ast.ClassDef
- ast.FunctionDef, ast.AsyncFunctionDef
- ast.arg
- ast.ExceptHandler
- ast.Name
"""
import ast
import typing

from get_child_nodes import get_child_nodes
from trie import TrieNode, search


def add_node_that_accesses_name(
        namespace_defining_trie_node: TrieNode[str, dict[str, set[ast.AST]]],
        node: ast.AST,
        name: str
):
    if namespace_defining_trie_node.value is None:
        namespace_defining_trie_node.value = {}

    if name not in namespace_defining_trie_node.value:
        namespace_defining_trie_node.value[name] = set()

    namespace_defining_trie_node.value[name].add(node)


class ModuleLevelASTNodeNamespaceTrieBuilder:
    def __init__(
        self,
        root: TrieNode[str, dict[str, set[ast.AST]]],
        module_name: str,
        module_node: ast.Module,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values: typing.Mapping[
            ast.AST,
            tuple[typing.Sequence[ast.AST], typing.Mapping[str, ast.AST], ast.AST]
        ]
    ):
        self.namespace_defining_trie_node_stack: list[TrieNode[str, dict[str, set[ast.AST]]]] = [root]
        self.module_node = module_node
        self.module_name = module_name
        self.function_definitions_to_parameters_name_parameter_mappings_and_return_values = function_definitions_to_parameters_name_parameter_mappings_and_return_values

    def visit(self, node: ast.AST):
        current_namespace_defining_trie_node = self.namespace_defining_trie_node_stack[-1]

        # ast.Module(body, type_ignores)
        if isinstance(node, ast.Module) and node == self.module_node:
            add_node_that_accesses_name(
                current_namespace_defining_trie_node,
                node,
                self.module_name,
            )

            new_namespace_defining_trie_node: TrieNode[str, dict[str, set[ast.AST]]] = TrieNode()
            current_namespace_defining_trie_node.children[self.module_name] = new_namespace_defining_trie_node
            self.namespace_defining_trie_node_stack.append(new_namespace_defining_trie_node)

            for child_node in get_child_nodes(node):
                self.visit(child_node)

            self.namespace_defining_trie_node_stack.pop()
        # ast.ClassDef(name, bases, keywords, body, decorator_list)
        elif isinstance(node, ast.ClassDef):
            add_node_that_accesses_name(
                current_namespace_defining_trie_node,
                node,
                node.name,
            )

            new_namespace_defining_trie_node: TrieNode[str, dict[str, set[ast.AST]]] = TrieNode()
            current_namespace_defining_trie_node.children[node.name] = new_namespace_defining_trie_node
            self.namespace_defining_trie_node_stack.append(new_namespace_defining_trie_node)

            for child_node in get_child_nodes(node):
                self.visit(child_node)

            self.namespace_defining_trie_node_stack.pop()
        # ast.FunctionDef(name, args, body, decorator_list, returns, type_comment)
        # ast.AsyncFunctionDef(name, args, body, decorator_list, returns, type_comment)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            add_node_that_accesses_name(
                current_namespace_defining_trie_node,
                node,
                node.name,
            )

            new_namespace_defining_trie_node: TrieNode[str, dict[str, set[ast.AST]]] = TrieNode()
            current_namespace_defining_trie_node.children[node.name] = new_namespace_defining_trie_node
            self.namespace_defining_trie_node_stack.append(new_namespace_defining_trie_node)

            # Add parameters and return value to namespace.
            if node in self.function_definitions_to_parameters_name_parameter_mappings_and_return_values:
                _, parameter_name_to_parameter_mapping, symbolic_return_value = self.function_definitions_to_parameters_name_parameter_mappings_and_return_values[node]
                for parameter_name, parameter in parameter_name_to_parameter_mapping.items():
                    add_node_that_accesses_name(
                        new_namespace_defining_trie_node,
                        parameter,
                        parameter_name,
                    )
                add_node_that_accesses_name(
                    new_namespace_defining_trie_node,
                    symbolic_return_value,
                    'return',
                )

            for child_node in get_child_nodes(node):
                self.visit(child_node)

            self.namespace_defining_trie_node_stack.pop()
        else:
            for child_node in get_child_nodes(node):
                self.visit(child_node)


def get_ast_node_namespace_trie(
    module_names: typing.Iterable[str],
    module_nodes: typing.Iterable[ast.Module],
    function_definitions_to_parameters_name_parameter_mappings_and_return_values: typing.Mapping[
        ast.AST,
        tuple[typing.Sequence[ast.AST], typing.Mapping[str, ast.AST], ast.AST]
    ]
) -> TrieNode[str, dict[str, set[ast.AST]]]:
    root: TrieNode[str, dict[str, set[ast.AST]]] = TrieNode()

    for module_name, module_node in zip(module_names, module_nodes):
        ModuleLevelASTNodeNamespaceTrieBuilder(
            root,
            module_name,
            module_node,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values
        ).visit(module_node)

    return root


def search_ast_node_namespace_trie(
    ast_node_namespace_trie_root_,
    components_: typing.Sequence[str]
) -> frozenset[ast.AST]:
    if components_:
        containing_namespace_components, name_ = components_[:-1], components_[-1]

        containing_namespace_trie_root = search(
            ast_node_namespace_trie_root_,
            containing_namespace_components
        )

        if containing_namespace_trie_root is not None:
            if containing_namespace_trie_root.value is not None:
                if name_ in containing_namespace_trie_root.value:
                    return frozenset(containing_namespace_trie_root.value[name_])

    return frozenset()

