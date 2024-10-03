import ast
import typing

from get_child_nodes import get_child_nodes


# Node in Python providing a function-like scope
NodeProvidingScope = typing.Union[
        ast.ClassDef,
        ast.FunctionDef,
        ast.AsyncFunctionDef,
        ast.Lambda,
        ast.ListComp,
        ast.SetComp,
        ast.DictComp,
        ast.GeneratorExp
]


def scoped_evaluation_order_node_visitor(
    node: ast.AST,
    callback: typing.Callable[
        [
            ast.AST,
            typing.Sequence[NodeProvidingScope]
        ],
        typing.Any
    ],
    scope_stack: typing.Sequence[NodeProvidingScope] = tuple(),
):
    # Modules
    if isinstance(node, ast.Module):
        callback(node, scope_stack)

        # Visit child nodes in default order
        for child_node in get_child_nodes(node):
            scoped_evaluation_order_node_visitor(child_node, callback, scope_stack)
    # Class definitions
    # Function definitions
    elif isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
        callback(node, scope_stack)

        # Adjust scope and visit child nodes
        new_scope_stack = scope_stack + (node,)
        for child_node in get_child_nodes(node):
            scoped_evaluation_order_node_visitor(child_node, callback, new_scope_stack)
    # Assignments
    # Visit from value to targets
    elif isinstance(node, ast.Assign):
        # Assign(expr* targets, expr value, string? type_comment)
        scoped_evaluation_order_node_visitor(node.value, callback, scope_stack)
        for target in reversed(node.targets):
            scoped_evaluation_order_node_visitor(target, callback, scope_stack)

        callback(node, scope_stack)
    elif isinstance(node, ast.AugAssign):
        # AugAssign(expr target, operator op, expr value)
        scoped_evaluation_order_node_visitor(node.value, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.op, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.target, callback, scope_stack)

        callback(node, scope_stack)
    elif isinstance(node, ast.AnnAssign):
        # AnnAssign(expr target, expr annotation, expr? value, int simple)
        if node.value is not None:
            scoped_evaluation_order_node_visitor(node.value, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.annotation, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.target, callback, scope_stack)

        callback(node, scope_stack)
    elif isinstance(node, ast.NamedExpr):
        # NamedExpr(expr target, expr value)
        scoped_evaluation_order_node_visitor(node.value, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.target, callback, scope_stack)

        callback(node, scope_stack)
    # Control-flow structures
    elif isinstance(node, (ast.For, ast.AsyncFor)):
        # For(expr target, expr iter, stmt* body, stmt* orelse, string? type_comment)
        # AsyncFor(expr target, expr iter, stmt* body, stmt* orelse, string? type_comment)
        scoped_evaluation_order_node_visitor(node.iter, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.target, callback, scope_stack)

        callback(node, scope_stack)

        for stmt in node.body + node.orelse:
            scoped_evaluation_order_node_visitor(stmt, callback, scope_stack)
    elif isinstance(node, ast.comprehension):
        # comprehension = (expr target, expr iter, expr* ifs, int is_async)
        scoped_evaluation_order_node_visitor(node.iter, callback, scope_stack)
        scoped_evaluation_order_node_visitor(node.target, callback, scope_stack)

        callback(node, scope_stack)

        for expr in node.ifs:
            scoped_evaluation_order_node_visitor(expr, callback, scope_stack)
    elif isinstance(node, (ast.While, ast.If)):
        # While(expr test, stmt* body, stmt* orelse)
        # If(expr test, stmt* body, stmt* orelse)
        scoped_evaluation_order_node_visitor(node.test, callback, scope_stack)

        callback(node, scope_stack)

        for stmt in node.body + node.orelse:
            scoped_evaluation_order_node_visitor(stmt, callback, scope_stack)
    elif isinstance(node, ast.Try):
        # Try(stmt* body, excepthandler* handlers, stmt* orelse, stmt* finalbody)
        callback(node, scope_stack)

        # Visit child nodes in default order
        for child_node in get_child_nodes(node):
            scoped_evaluation_order_node_visitor(child_node, callback, scope_stack)
    elif isinstance(node, ast.excepthandler):
        # excepthandler = ExceptHandler(expr? type, identifier? name, stmt* body)
        if node.type is not None:
            scoped_evaluation_order_node_visitor(node.type, callback, scope_stack)
        
        callback(node, scope_stack)

        for stmt in node.body:
            scoped_evaluation_order_node_visitor(stmt, callback, scope_stack)
    elif isinstance(node, (ast.With, ast.AsyncWith)):
        # With(withitem* items, stmt* body, string? type_comment)
        # AsyncWith(withitem* items, stmt* body, string? type_comment)
        for withitem in node.items:
            scoped_evaluation_order_node_visitor(withitem, callback, scope_stack)

        callback(node, scope_stack)

        for stmt in node.body:
            scoped_evaluation_order_node_visitor(stmt, callback, scope_stack)
    # Comprehensions
    elif isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp)):
        # ListComp(expr elt, comprehension * generators)
        # SetComp(expr elt, comprehension * generators)
        # GeneratorExp(expr elt, comprehension * generators)

        # Adjust scope and visit child nodes
        # Visit generators before visiting elt
        new_scope_stack = scope_stack + (node,)
        for generator in node.generators:
            scoped_evaluation_order_node_visitor(generator, callback, new_scope_stack)
        scoped_evaluation_order_node_visitor(node.elt, callback, new_scope_stack)

        callback(node, scope_stack)
    elif isinstance(node, ast.DictComp):
        # DictComp(expr key, expr value, comprehension * generators)

        # Adjust scope and visit child nodes
        # Visit generators before visiting key, value
        new_scope_stack = scope_stack + (node,)
        for generator in node.generators:
            scoped_evaluation_order_node_visitor(generator, callback, new_scope_stack)
        scoped_evaluation_order_node_visitor(node.key, callback, new_scope_stack)
        scoped_evaluation_order_node_visitor(node.value, callback, new_scope_stack)

        callback(node, scope_stack)
    # Other statements and expressions
    else:
        # Visit child nodes in default order
        for child_node in get_child_nodes(node):
            scoped_evaluation_order_node_visitor(child_node, callback, scope_stack)

        callback(node, scope_stack)
