import ast
import collections
import itertools
import typing

from ast import AST
from typing import Any, Callable, Dict, Iterable, Mapping, Optional, Sequence, Tuple

from get_attribute_access_result import get_attribute_access_result
from get_attributes_in_runtime_class import get_attributes_in_runtime_class
from get_call_information import get_call_information
from get_parameters import get_parameters
from handle_function_call import handle_function_call
from relations import RelationType
from scoped_evaluation_order_node_visitor import NodeProvidingScope, scoped_evaluation_order_node_visitor
from type_definitions import (
    RuntimeClass,
    UnwrappedRuntimeFunction,
    FunctionDefinition,
    Instance,
    RuntimeTerm
)
from typeshed_client_ex.client import Client
from unwrap import unwrap


UNARY_OP_TO_ATTRIBUTE: Dict[type, str] = {
    ast.Invert: '__invert__',
    ast.UAdd: '__pos__',
    ast.USub: '__neg__'
}

BINARY_OP_TO_ATTRIBUTE: Dict[type, str] = {
    ast.Add: '__add__',
    ast.Sub: '__sub__',
    ast.Mult: '__mul__',
    ast.MatMult: '__matmul__',
    ast.Div: '__truediv__',
    ast.Mod: '__mod__',
    ast.Pow: '__pow__',
    ast.LShift: '__lshift__',
    ast.RShift: '__rshift__',
    ast.BitOr: '__or__',
    ast.BitXor: '__xor__',
    ast.BitAnd: '__and__',
    ast.FloorDiv: '__floordiv__'
}

CMPOP_TO_ATTRIBUTE: Dict[type, str] = {
    ast.Eq: '__eq__',
    ast.NotEq: '__ne__',
    ast.Lt: '__lt__',
    ast.LtE: '__le__',
    ast.Gt: '__gt__',
    ast.GtE: '__ge__'
}


def handle_local_syntax_directed_typing_constraints(
    module_node: ast.Module,
    top_level_class_definitions_to_runtime_classes: Mapping[ast.ClassDef, RuntimeClass],
    unwrapped_runtime_functions_to_named_function_definitions: Mapping[UnwrappedRuntimeFunction, FunctionDefinition],
    function_definitions_to_parameters_name_parameter_mappings_and_return_values: Mapping[FunctionDefinition, Tuple[Sequence[AST], Mapping[str, AST], AST]],
    node_to_definition_node_mapping: Mapping[AST, AST],
    get_runtime_terms_callback: Callable[[AST], Iterable[RuntimeTerm]],
    update_runtime_terms_callback: Callable[[AST, Iterable[RuntimeTerm]], Any],
    update_bag_of_attributes_callback: Callable[[AST, Iterable[str]], Any],
    add_subset_callback: Callable[[AST, AST], Any],
    add_relation_callback: Callable[[AST, AST, RelationType, Optional[object]], Any],
    typeshed_client: Client
):
    def get_runtime_terms_of_definition_node(node: AST):
        nonlocal node_to_definition_node_mapping

        # Get the definition node, if it has one
        definition_node = node_to_definition_node_mapping.get(node, node)

        # Return the result of calling get_runtime_terms_callback on the definition node
        return get_runtime_terms_callback(definition_node)
    
    def update_runtime_terms_of_definition_node(node: AST, runtime_terms: Iterable[RuntimeTerm]):
        nonlocal node_to_definition_node_mapping

        # Get the definition node, if it has one
        definition_node = node_to_definition_node_mapping.get(node, node)

        # Return the result of calling update_runtime_terms_callback on the definition node
        return update_runtime_terms_callback(definition_node, runtime_terms)

    def update_runtime_terms_and_bag_of_attributes_from_runtime_class(
        node: AST,
        runtime_class: RuntimeClass
    ):
        if runtime_class not in (type(None), type(Ellipsis), type(NotImplemented)):
            update_runtime_terms_of_definition_node(node, {Instance(runtime_class)})
            update_bag_of_attributes_callback(node, get_attributes_in_runtime_class(runtime_class))
    
    def set_equivalent(
        first: AST,
        second: AST
    ):
        add_subset_callback(first, second)
        add_subset_callback(second, first)
    
    def handle_local_syntax_directed_typing_constraints_callback(
        node: AST,
        scope_stack: list[NodeProvidingScope]
    ):        
        # Literals
        # ast.Constant(value)
        if isinstance(node, ast.Constant):
            # Set the current type variable to be an instance of `type(value)`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, type(node.value))
        # ast.JoinedStr(values)
        elif isinstance(node, ast.JoinedStr):
            # Set the current type variable to be an instance of `str`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, str)
        # ast.List(elts, ctx)
        elif isinstance(node, ast.List):
            # Set the current type variable to be an instance of `list`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, list)

            for elt in node.elts:
                if not isinstance(elt, ast.Starred):
                    # Set `elt` as $ValueOf$ and $IterTargetOf$ the current type variable
                    add_relation_callback(node, elt, RelationType.ValueOf, None)
                    add_relation_callback(node, elt, RelationType.IterTargetOf, None)
        # ast.Tuple(elts, ctx)
        elif isinstance(node, ast.Tuple):
            # Set the current type variable to be an instance of `tuple`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, tuple)

            if not any((isinstance(elt, ast.Starred) for elt in node.elts)):
                for i, elt in enumerate(node.elts):
                    # Set `elt` as the $i$-th $ElementOf$ the current type variable
                    add_relation_callback(node, elt, RelationType.ElementOf, i)
        # ast.Set(elts)
        elif isinstance(node, ast.Set):
            # Set the current type variable to be an instance of `set`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, set)

            for elt in node.elts:
                if not isinstance(elt, ast.Starred):
                    # Set `elt` as $IterTargetOf$ the current type variable
                    add_relation_callback(node, elt, RelationType.IterTargetOf, None)
        # ast.Dict(keys, values)
        elif isinstance(node, ast.Dict):
            # Set the current type variable to be an instance of `dict`
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, dict)

            for key, value in zip(node.keys, node.values):
                if key is not None:
                    # Set `key` as $KeyOf$ and $IterTargetOf$ the current type variable
                    add_relation_callback(node, key, RelationType.KeyOf, None)
                    add_relation_callback(node, key, RelationType.IterTargetOf, None)
                    # Set `value` as $ValueOf$ the current type variable
                    add_relation_callback(node, value, RelationType.ValueOf, None)
        # Variables
        # ast.Starred(value, ctx)
        elif isinstance(node, ast.Starred):
            # Set `value` to be an instance of `collections.abc.Iterable`
            # according to https://docs.python.org/3/reference/expressions.html#grammar-token-python-grammar-starred_expression)
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node.value, collections.abc.Iterable)
        # Expressions
        # ast.UnaryOp(op, operand)
        elif isinstance(node, ast.UnaryOp):
            if isinstance(node.op, (ast.Invert, ast.UAdd, ast.USub)):
                # Update the attribute counter of `operand` with the attribute corresponding to `op`.
                update_bag_of_attributes_callback(node.operand, {UNARY_OP_TO_ATTRIBUTE[type(node.op)]})

                # Set the current type variable as equivalent to `operand`.
                set_equivalent(node, node.operand)
            elif isinstance(node.op, ast.Not):
                # Set the current type variable as equivalent to `bool`.
                update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, bool)
        # ast.BinOp(left, op, right)
        elif isinstance(node, ast.BinOp):
            # Note that some of these operations also apply to certain non-numeric types.
            # https://docs.python.org/3/reference/expressions.html#binary-arithmetic-operations

            # Update the attribute counter of `left` with the attribute corresponding to `op`.
            update_bag_of_attributes_callback(node.left, {BINARY_OP_TO_ATTRIBUTE[type(node.op)]})

            # The * (multiplication) operator yields the product of its arguments.
            # The arguments must either both be numbers, or one argument must be an integer and the other must be a sequence.
            # In the former case, the numbers are converted to a common type and then multiplied together.
            # In the latter case, sequence repetition is performed; a negative repetition factor yields an empty sequence.
            if isinstance(node.op, ast.Mult):
                pass
            # In addition to performing the modulo operation on numbers,
            # the % operator is also overloaded by string objects to perform old-style string formatting (also known as interpolation).
            # The syntax for string formatting is described in the Python Library Reference, section printf-style String Formatting.
            elif isinstance(node.op, ast.Mod):
                set_equivalent(node, node.left)
            else:
                set_equivalent(node, node.left)
                set_equivalent(node.left, node.right)
        # ast.Compare(left, ops, comparators)
        elif isinstance(node, ast.Compare):
            operands = [node.left] + node.comparators
            for (left, right), op in zip(
                    itertools.pairwise(operands),
                    node.ops
            ):
                if isinstance(op, (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                    # Update the attribute counter of `left` with the attribute corresponding to `op`.
                    update_bag_of_attributes_callback(left, {CMPOP_TO_ATTRIBUTE[type(op)]})

                    # Set `left` as equivalent to `right`.
                    set_equivalent(left, right)
                elif isinstance(op, (ast.In, ast.NotIn)):
                    # based on https://docs.python.org/3/reference/expressions.html#membership-test-operations and https://discuss.python.org/t/deprecate-old-style-iteration-protocol/17863/7
                    # Update the attribute counter of `right` with the attributes `__contains__` and `__iter__`.
                    update_bag_of_attributes_callback(right, {'__contains__', '__iter__'})

                    # Set `left` as $IterTargetOf$ `right`.
                    add_relation_callback(right, left, RelationType.IterTargetOf, None)

                    # Set the current type variable as equivalent to `bool`.
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, bool)
        # ast.Call(func, args, keywords, starargs, kwargs)
        elif isinstance(node, ast.Call):
            (
                func,
                non_starred_arguments,
                keyword_args_to_values,
                contains_starred_arguments_or_keywords
            ) = get_call_information(node)

            # Update the attribute counter of `func` with the attribute `__call__`.
            update_bag_of_attributes_callback(func, {'__call__'})

            # Handle function call for all runtime terms
            for runtime_term in get_runtime_terms_of_definition_node(func):
                handle_function_call(
                    runtime_term,
                    non_starred_arguments,
                    keyword_args_to_values,
                    node,
                    unwrapped_runtime_functions_to_named_function_definitions,
                    function_definitions_to_parameters_name_parameter_mappings_and_return_values,
                    get_runtime_terms_of_definition_node,
                    update_runtime_terms_of_definition_node,
                    update_bag_of_attributes_callback,
                    add_subset_callback,
                    typeshed_client
                )
            
            # Add relations
            if contains_starred_arguments_or_keywords:              
                # Create a dummy node to represent all parameters.
                # Add ... to the runtime values of that dummy node.
                # Set that dummy node the $i$-th $ParameterOf$ `func`.
                dummy_node_representing_all_parameters = AST()

                if (lineno := getattr(node, 'lineno', None)) is not None:
                    setattr(dummy_node_representing_all_parameters, 'lineno', lineno)

                if (col_offset := getattr(node, 'col_offset', None)) is not None:
                    setattr(dummy_node_representing_all_parameters, 'col_offset', col_offset)
                
                if (end_lineno := getattr(node, 'end_lineno', None)) is not None:
                    setattr(dummy_node_representing_all_parameters, 'end_lineno', end_lineno)
                
                if (end_col_offset := getattr(node, 'end_col_offset', None)) is not None:
                    setattr(dummy_node_representing_all_parameters, 'end_col_offset', end_col_offset)
                    
                update_runtime_terms_of_definition_node(dummy_node_representing_all_parameters, {Instance(type(Ellipsis))})

                add_relation_callback(func, dummy_node_representing_all_parameters, RelationType.ParameterOf, 0)
            else:
                # Set `arg` as the $i$-th $ParameterOf$ `func`.
                for i, argument in enumerate(non_starred_arguments):
                    add_relation_callback(func, argument, RelationType.ParameterOf, i)
            
            # Set the current type variable as the $ReturnValueOf$ `func`.
            add_relation_callback(func, node, RelationType.ReturnValueOf, None)
        # ast.IfExp(test, body, orelse)
        elif isinstance(node, ast.IfExp):
            add_subset_callback(node, node.body)
            add_subset_callback(node, node.orelse)
        # ast.Attribute(value, attr, ctx)
        elif isinstance(node, ast.Attribute):
            # Update the attribute counter of `value` with `attr`.
            update_bag_of_attributes_callback(node.value, {node.attr})

            # Get the runtime terms in `value`
            # Get the attribute access results
            attribute_access_results = set()
            for runtime_term in get_runtime_terms_of_definition_node(node.value):
                attribute_access_result = get_attribute_access_result(
                    runtime_term,
                    node.attr,
                    unwrapped_runtime_functions_to_named_function_definitions
                )

                if attribute_access_result is not None:
                    attribute_access_results.add(attribute_access_result)
            
            # Add the runtime terms to the node
            update_runtime_terms_of_definition_node(node, attribute_access_results)
        # ast.NamedExpr(target, value)
        elif isinstance(node, ast.NamedExpr):
            # Set the current type variable as equivalent to `target` and `value`.
            set_equivalent(node.target, node.value)
            set_equivalent(node, node.target)

            # Transfer runtime terms from `value` to `target`.
            update_runtime_terms_of_definition_node(
                node.target,
                get_runtime_terms_of_definition_node(
                    node.value
                )
            )
        # Subscripting
        # ast.Subscript(value, slice, ctx)
        elif isinstance(node, ast.Subscript):
            if isinstance(node.slice, (ast.Tuple, ast.Slice)):
                if isinstance(node.ctx, ast.Load):
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(node.value, collections.abc.Sequence)
                elif isinstance(node.ctx, ast.Store):
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(node.value, collections.abc.MutableSequence)
                
                # Set the current type variable as equivalent to `value`.
                set_equivalent(node, node.value)
            else:
                if isinstance(node.ctx, ast.Load):
                    update_bag_of_attributes_callback(node.value, {'__getitem__'})
                elif isinstance(node.ctx, ast.Store):
                    update_bag_of_attributes_callback(node.value, {'__setitem__'})
                
                # Set `slice` as $KeyOf$ `value`.
                add_relation_callback(node.value, node.slice, RelationType.KeyOf, None)
                # Set the current type variable as $ValueOf$ `value`.
                add_relation_callback(node.value, node, RelationType.ValueOf, None)
        # ast.Slice(lower, upper, step)
        elif isinstance(node, ast.Slice):
            # Set the current type variable as equivalent to `slice`.
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, slice)

            for value in (node.lower, node.upper, node.step):
                if value is not None:
                    # Set `value` as equivalent to `int`.
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(value, int)
        # Comprehensions
        # ast.ListComp(elt, generators)
        elif isinstance(node, ast.ListComp):
            # Set the current type variable as equivalent to `list`.
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, list)

            # Set `elt` as $ValueOf$ and $IterTargetOf$ the current type variable.
            add_relation_callback(node, node.elt, RelationType.ValueOf, None)
            add_relation_callback(node, node.elt, RelationType.IterTargetOf, None)
        # ast.SetComp(elt, generators)
        elif isinstance(node, ast.SetComp):
            # Set the current type variable as equivalent to `set`.
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, set)

            # Set `elt` as $IterTargetOf$ the current type variable.
            add_relation_callback(node, node.elt, RelationType.IterTargetOf, None)
        # ast.GeneratorExp(elt, generators)
        elif isinstance(node, ast.GeneratorExp):
            # Set the current type variable as equivalent to `collections.abc.Generator`.
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, collections.abc.Generator)

            # Set `elt` as $IterTargetOf$ the current type variable.
            add_relation_callback(node, node.elt, RelationType.IterTargetOf, None)
        # ast.DictComp(key, value, generators)
        elif isinstance(node, ast.DictComp):
            # Set the current type variable as equivalent to `dict`.
            update_runtime_terms_and_bag_of_attributes_from_runtime_class(node, dict)

            # Set `key` as $KeyOf$ and $IterTargetOf$ the current type variable.
            add_relation_callback(node, node.key, RelationType.KeyOf, None)
            add_relation_callback(node, node.key, RelationType.IterTargetOf, None)

            # Set `value` as $ValueOf$ the current type variable.
            add_relation_callback(node, node.value, RelationType.ValueOf, None)
        # ast.comprehension(target, iter, ifs, is_async)
        elif isinstance(node, ast.comprehension):
            if node.is_async:
                # Update the attribute counter of `iter` with the attribute `__aiter__`.
                update_bag_of_attributes_callback(node.iter, {'__aiter__'})
            else:
                # Update the attribute counter of `iter` with the attribute `__iter__`.
                update_bag_of_attributes_callback(node.iter, {'__iter__'})
            # Set `target` as $IterTargetOf$ `iter`.
            add_relation_callback(node.iter, node.target, RelationType.IterTargetOf, None)
        # Statements
        # ast.Assign(targets, value, type_comment)
        elif isinstance(node, ast.Assign):
            for (value, target) in itertools.pairwise(
                reversed(node.targets + [node.value])
            ):
                set_equivalent(target, value)
                
                # Transfer runtime terms from `value` to `target`.
                update_runtime_terms_of_definition_node(
                    target,
                    get_runtime_terms_of_definition_node(
                        value
                    )
                )
        # ast.AnnAssign(target, annotation, value, simple)
        elif isinstance(node, ast.AnnAssign):
            if node.value is not None:
                set_equivalent(node.target, node.value)

                # Transfer runtime terms from `value` to `target`.
                update_runtime_terms_of_definition_node(
                    node.target,
                    get_runtime_terms_of_definition_node(
                        node.value
                    )
                )
        # ast.AugAssign(target, op, value)
        elif isinstance(node, ast.AugAssign):
            # Update the attribute counter of `target` with the attribute corresponding to `op`.
            update_bag_of_attributes_callback(node.target, {BINARY_OP_TO_ATTRIBUTE[type(node.op)]})

            set_equivalent(node.target, node.value)
        # Imports
        # Control flow
        # ast.For(target, iter, body, orelse, type_comment)
        elif isinstance(node, ast.For):
            # Update the attribute counter of `iter` with the attribute `__iter__`.
            update_bag_of_attributes_callback(node.iter, {'__iter__'})

            # Set `target` as $IterTargetOf$ `iter`.
            add_relation_callback(node.iter, node.target, RelationType.IterTargetOf, None)
        # ast.AsyncFor(target, iter, body, orelse, type_comment)
        elif isinstance(node, ast.AsyncFor):
            # Update the attribute counter of `iter` with the attribute `__aiter__`.
            update_bag_of_attributes_callback(node.iter, {'__aiter__'})

            # Set `target` as $IterTargetOf$ `iter`.
            add_relation_callback(node.iter, node.target, RelationType.IterTargetOf, None)
        # ast.With(items, body, type_comment)
        elif isinstance(node, ast.With):
            for withitem in node.items:
                # Update the attribute counter of `withitem.context_expr` with the attributes `__enter__`, `__exit__`.
                update_bag_of_attributes_callback(withitem.context_expr, {'__enter__', '__exit__'})
        # ast.AsyncWith(items, body, type_comment)
        elif isinstance(node, ast.AsyncWith):
            for withitem in node.items:
                # Update the attribute counter of `withitem.context_expr` with the attributes `__aenter__`, `__aexit__`.
                update_bag_of_attributes_callback(withitem.context_expr, {'__aenter__', '__aexit__'})
        # Function and class definitions
        # ast.FunctionDef(name, args, body, decorator_list, returns, type_comment, type_params)
        # ast.AsyncFunctionDef(name, args, body, decorator_list, returns, type_comment, type_params)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Add runtime terms
            update_runtime_terms_of_definition_node(node, {node})

            # Update the attribute counter with the attribute `__call__`
            update_bag_of_attributes_callback(node, {'__call__'})
            
            # Add relations
            if node in function_definitions_to_parameters_name_parameter_mappings_and_return_values:
                (
                    _,
                    _,
                    return_value
                ) = function_definitions_to_parameters_name_parameter_mappings_and_return_values[node]
            
                posargs, vararg, kwonlyargs, kwarg = get_parameters(node)

                if vararg or kwonlyargs or kwarg:
                    # Create a dummy node to represent all parameters.
                    # Add ... to the runtime values of that dummy node.
                    dummy_node_representing_all_parameters = node.args
                    update_runtime_terms_of_definition_node(dummy_node_representing_all_parameters, {Instance(type(Ellipsis))})

                    add_relation_callback(node, dummy_node_representing_all_parameters, RelationType.ParameterOf, 0)
                else:
                    for i, argument in enumerate(posargs):
                        add_relation_callback(node, argument, RelationType.ParameterOf, i)
            
                add_relation_callback(node, return_value, RelationType.ReturnValueOf, None)

                # Handle return values

                is_async = isinstance(node, ast.AsyncFunctionDef)
                apparent_return_value_set = set()
                yield_value_set = set()
                send_value_set = set()
                returns_generator = False

                def handle_return_values_callback(
                    node_: AST,
                    scope_stack_: list[NodeProvidingScope]
                ):
                    nonlocal apparent_return_value_set, yield_value_set, send_value_set, returns_generator
                    # ast.Return(value)
                    if isinstance(node_, ast.Return):
                        if scope_stack_[-1] == node and node_.value is not None:
                            apparent_return_value_set.add(node_.value)
                    # ast.Yield(value)
                    elif isinstance(node_, ast.Yield):
                        if scope_stack_[-1] == node:
                            if node_.value is not None:
                                yield_value_set.add(node_.value)

                            send_value_set.add(node_)

                            returns_generator = True
                    # ast.YieldFrom(value)
                    elif isinstance(node_, ast.YieldFrom):
                        if scope_stack_[-1] == node:
                            returns_generator = True
                
                scoped_evaluation_order_node_visitor(
                    node,
                    handle_return_values_callback,
                    scope_stack
                )

                # non-async functions returning generators
                if not is_async and returns_generator:
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(return_value, collections.abc.Generator)

                    for yield_value in yield_value_set:
                        add_relation_callback(return_value, yield_value, RelationType.IterTargetOf, None)

                    for send_value in send_value_set:
                        add_relation_callback(return_value, send_value, RelationType.SendTargetOf, None)

                    for apparent_return_value in apparent_return_value_set:
                        add_relation_callback(return_value, apparent_return_value, RelationType.YieldFromAwaitResultOf, None)
                # async functions returning generators
                elif is_async and returns_generator:
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(return_value, collections.abc.AsyncGenerator)

                    for yield_value in yield_value_set:
                        add_relation_callback(return_value, yield_value, RelationType.IterTargetOf, None)

                    for send_value in send_value_set:
                        add_relation_callback(return_value, send_value, RelationType.SendTargetOf, None)
                # async functions not returning generators
                elif is_async and not returns_generator:
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(return_value, collections.abc.Coroutine)

                    for yield_value in yield_value_set:
                        add_relation_callback(return_value, yield_value, RelationType.IterTargetOf, None)

                    for send_value in send_value_set:
                        add_relation_callback(return_value, send_value, RelationType.SendTargetOf, None)

                    for apparent_return_value in apparent_return_value_set:
                        add_relation_callback(return_value, apparent_return_value, RelationType.YieldFromAwaitResultOf, None)
                # non-async functions not returning generators
                else:
                    # Criterion for judging that a function MUST return None:
                    # NOT ASYNC, DOES NOT RETURN GENERATOR, NO RETURN STATEMENT RETURNING A VALUE
                    # is async -> must not return None
                    # contains a same-level yield or yield from expression -> must not return None
                    # contains a same-level return statement returning a value -> might not always return None
                    if not apparent_return_value_set:
                        update_runtime_terms_of_definition_node(return_value, {Instance(type(None))})
                    else:
                        for apparent_return_value in apparent_return_value_set:
                            add_subset_callback(return_value, apparent_return_value)
        # ast.Lambda(args, body)
        elif isinstance(node, ast.Lambda):
            # Add runtime terms
            update_runtime_terms_of_definition_node(node, {node})

            # Update the attribute counter with the attribute `__call__`
            update_bag_of_attributes_callback(node, {'__call__'})
            
            # Add relations
            posargs, vararg, kwonlyargs, kwarg = get_parameters(node)

            if vararg or kwonlyargs or kwarg:
                # Create a dummy node to represent all parameters.
                # Add ... to the runtime values of that dummy node.
                dummy_node_representing_all_parameters = node.args
                update_runtime_terms_of_definition_node(dummy_node_representing_all_parameters, {Instance(type(Ellipsis))})

                add_relation_callback(node, dummy_node_representing_all_parameters, RelationType.ParameterOf, 0)
            else:
                for i, argument in enumerate(posargs):
                    add_relation_callback(node, argument, RelationType.ParameterOf, i)
        
            add_relation_callback(node, node.body, RelationType.ReturnValueOf, None)

            if node in function_definitions_to_parameters_name_parameter_mappings_and_return_values:
                (
                    _,
                    _,
                    return_value
                ) = function_definitions_to_parameters_name_parameter_mappings_and_return_values[node]

                # Handle return values
                add_subset_callback(return_value, node.body)
        # ast.arguments(posonlyargs, args, vararg, kwonlyargs, kw_defaults, kwarg, defaults)
        elif isinstance(node, ast.arguments):
            # Handle the default values of parameters.
            posargs = node.posonlyargs + node.args
            kwonlyargs = node.kwonlyargs

            # N posargs_defaults align with the *last* N posargs
            # N kw_defaults align with N kwonlyargs (though they may be None's)
            posargs_defaults = node.defaults
            kwonlyargs_defaults = node.kw_defaults

            for posarg, posarg_default in zip(
                reversed(posargs),
                reversed(posargs_defaults)
            ):
                add_subset_callback(posarg, posarg_default)

            for kwonlyarg, kwonlyarg_default in zip(
                kwonlyargs,
                kwonlyargs_defaults
            ):
                if kwonlyarg_default is not None:
                    add_subset_callback(kwonlyarg, kwonlyarg_default)
        # ast.YieldFrom(value)
        elif isinstance(node, ast.YieldFrom):
            # Update the attribute counter of `value` with the attribute `__iter__`.
            update_bag_of_attributes_callback(node.value, {'__iter__'})
            
            # Set the current type variable as the $YieldFromAwaitResultOf$ `value`.
            add_relation_callback(node.value, node, RelationType.YieldFromAwaitResultOf, None)
        # ast.Await(value)
        elif isinstance(node, ast.Await):
            # Update the attribute counter of `value` with the attribute `__await__`.
            update_bag_of_attributes_callback(node.value, {'__await__'})

            # Set the current type variable as the $YieldFromAwaitResultOf$ of `value`
            add_relation_callback(node.value, node, RelationType.YieldFromAwaitResultOf, None)
        # ast.ClassDef(name, bases, keywords, body, decorator_list, type_params)
        elif isinstance(node, ast.ClassDef):
            # Update the attribute counter with the attributes in `type`
            update_bag_of_attributes_callback(node, get_attributes_in_runtime_class(type))
            
            if node in top_level_class_definitions_to_runtime_classes:
                runtime_class = top_level_class_definitions_to_runtime_classes[node]

                # Add runtime terms
                update_runtime_terms_of_definition_node(node, {runtime_class})

                # `self` of all instance methods within a runtime class are equivalent and are instances of the runtime class.
                # `cls` of all classmethods within a runtime class contain the class definition as a runtime term.
                first_parameter_of_instance_methods = set()
                first_parameter_of_classmethods = set()

                for _, v in runtime_class.__dict__.items():
                    is_staticmethod = isinstance(v, staticmethod)
                    is_classmethod = isinstance(v, classmethod)

                    unwrapped_v = unwrap(v)

                    if isinstance(unwrapped_v, UnwrappedRuntimeFunction) and unwrapped_v in unwrapped_runtime_functions_to_named_function_definitions:
                        function_definition = unwrapped_runtime_functions_to_named_function_definitions[unwrapped_v]

                        (
                            parameter_list,
                            _,
                            _
                        ) = function_definitions_to_parameters_name_parameter_mappings_and_return_values[function_definition]

                        if parameter_list:
                            first_parameter = parameter_list[0]

                            if is_classmethod:
                                first_parameter_of_classmethods.add(first_parameter)
                            if not is_staticmethod and not is_classmethod:
                                first_parameter_of_instance_methods.add(first_parameter)

                for first_parameter_of_instance_method in first_parameter_of_instance_methods:
                    update_runtime_terms_and_bag_of_attributes_from_runtime_class(first_parameter_of_instance_method, runtime_class)

                for first_parameter_of_classmethod in first_parameter_of_classmethods:
                    update_runtime_terms_of_definition_node(first_parameter_of_classmethod, {runtime_class})

    return scoped_evaluation_order_node_visitor(
        module_node,
        handle_local_syntax_directed_typing_constraints_callback
    )
