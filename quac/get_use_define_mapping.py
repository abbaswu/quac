"""
https://en.wikipedia.org/wiki/Use-define_chain
"""

import ast
import itertools
import typing

from disjoint_set import DisjointSet
from scoped_evaluation_order_node_visitor import NodeProvidingScope, scoped_evaluation_order_node_visitor


def get_scope(
    scope_stack: typing.Sequence[NodeProvidingScope],
):
    if scope_stack:
        current_scope_or_none = scope_stack[-1]
    else:
        current_scope_or_none = None
    
    return current_scope_or_none


def get_use_define_mapping(
    module_node: ast.Module,
    global_names_to_definition_nodes: typing.Mapping[str, ast.AST]
):
    scope_to_names_to_definition_nodes: dict[
        typing.Optional[NodeProvidingScope],
        typing.Mapping[str, ast.AST]
    ] = {
        None: global_names_to_definition_nodes
    }

    # Requires considering both the class stack and the scope stack
    def get_definition(
        scope_stack: typing.Sequence[NodeProvidingScope],
        name: str
    ) -> typing.Optional[ast.AST]:
        nonlocal scope_to_names_to_definition_nodes

        current_scope_or_none = get_scope(scope_stack)

        definition_node_or_none: typing.Optional[ast.AST] = None
        scope_or_none: typing.Optional[ast.AST] = None

        # Is the name within the current scope?
        if name in (names_to_definition_nodes := scope_to_names_to_definition_nodes.setdefault(
            current_scope_or_none,
            {}
        )):
            # Directly retrieve the definition node
            definition_node_or_none = names_to_definition_nodes[name]
            scope_or_none = current_scope_or_none
        # Otherwise, the name may be (implicitly) global or nonlocal
        else:
            for containing_scope in itertools.chain(reversed(scope_stack[:-1]), (None,)):
                local_names_to_definition_nodes = scope_to_names_to_definition_nodes.setdefault(containing_scope, {})
                if name in local_names_to_definition_nodes:
                    definition_node_or_none = local_names_to_definition_nodes[name]
                    scope_or_none = containing_scope
                    break

        return definition_node_or_none, scope_or_none
    
    def set_definition_node(
        scope_stack: typing.Sequence[NodeProvidingScope],
        name: str,
        definition_node: ast.AST
    ):
        nonlocal scope_to_names_to_definition_nodes

        current_scope_or_none = get_scope(scope_stack)
        scope_to_names_to_definition_nodes.setdefault(current_scope_or_none, {})[name] = definition_node

    use_define_mapping: DisjointSet[ast.AST] = DisjointSet()     
    
    def handle_scoped_name_access_node(
        scope_stack: typing.Sequence[NodeProvidingScope],
        name: str,
        node: ast.AST,
        is_definition: bool
    ):
        nonlocal use_define_mapping

        current_scope_or_none = get_scope(scope_stack)
        
        (
            previous_definition_node_or_none,
            previous_definition_scope_or_none
        ) = get_definition(scope_stack, name)

        if previous_definition_node_or_none is not None:
            # If is_definition is True, the previous definition node is in fact only valid if is within the current scope.
            # Otherwise, we are shadowing a name from an outer scope.
            if (not is_definition) or (is_definition and previous_definition_scope_or_none == current_scope_or_none):
                use_define_mapping.union(node, previous_definition_node_or_none)
        
        if is_definition:
            set_definition_node(scope_stack, name, node)

    def handle_global_node(
        scope_stack: typing.Sequence[NodeProvidingScope],
        node: ast.Global
    ):
        nonlocal use_define_mapping

        for name in node.names:
            # Look up global definition node for name
            global_definition_node_or_none, _ = get_definition(tuple(), name)

            # Create dummy global definition node if necessary
            if global_definition_node_or_none is not None:
                global_definition_node = global_definition_node_or_none
            else:
                global_definition_node = ast.AST()
                setattr(global_definition_node, 'id', name)
                set_definition_node(tuple(), name, global_definition_node)
            
            set_definition_node(scope_stack, name, node)
            use_define_mapping.union(node, global_definition_node)
    
    def handle_nonlocal_node(
        scope_stack: typing.Sequence[NodeProvidingScope],
        node: ast.Global
    ):
        nonlocal use_define_mapping

        for name in node.names:
            # Look up nonlocal definition node for name
            nonlocal_definition_node_or_none, _ = get_definition(scope_stack[:-1], name)

            if nonlocal_definition_node_or_none is not None:
                nonlocal_definition_node = nonlocal_definition_node_or_none
                use_define_mapping.union(node, nonlocal_definition_node)
            
            set_definition_node(scope_stack, name, node)

    def module_level_name_resolution_callback(
            node: ast.AST,
            scope_stack: typing.Sequence[NodeProvidingScope],
    ):
        # ast.Name(id, ctx)
        if isinstance(node, ast.Name):
            handle_scoped_name_access_node(scope_stack, node.id, node, isinstance(node.ctx, ast.Store))
        # ast.FunctionDef(name, args, body, decorator_list, returns, type_comment)
        # ast.AsyncFunctionDef(name, args, body, decorator_list, returns, type_comment)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            handle_scoped_name_access_node(scope_stack, node.name, node, True)
        # ast.arg(arg, annotation, type_comment)
        elif isinstance(node, ast.arg):
            handle_scoped_name_access_node(scope_stack, node.arg, node, True)
        # ast.ClassDef(name, bases, keywords, starargs, kwargs, body, decorator_list)
        elif isinstance(node, ast.ClassDef):
            handle_scoped_name_access_node(scope_stack, node.name, node, True)
        # ast.alias(name, asname)
        elif isinstance(node, ast.alias):
            if node.asname is not None:
                handle_scoped_name_access_node(scope_stack, node.asname, node, True)
            elif node.name is not None:
                handle_scoped_name_access_node(scope_stack, node.name, node, True)
        # ast.ExceptHandler(type, name, body)
        elif isinstance(node, ast.ExceptHandler):
            if node.name is not None:
                handle_scoped_name_access_node(scope_stack, node.name, node, True)
        # ast.Global(names)
        elif isinstance(node, ast.Global):
            handle_global_node(scope_stack, node)
        # ast.Nonlocal(names)
        elif isinstance(node, ast.Nonlocal):
            handle_nonlocal_node(scope_stack, node)

    # Run callbacks to initialize global scope.
    for global_name, definition_node in global_names_to_definition_nodes.items():
        set_definition_node(tuple(), global_name, definition_node)

    # Visit nodes in the module.
    scoped_evaluation_order_node_visitor(module_node, module_level_name_resolution_callback)

    return use_define_mapping 
