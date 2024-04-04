"""Utilities for type argument inference."""

from typing import List, Optional, Sequence, NamedTuple

from extyper.constraints import (
    infer_constraints, infer_constraints_for_callable, SUBTYPE_OF, SUPERTYPE_OF, infer_constraints_for_callable_pure
)
from extyper.types import Type, TypeVarId, CallableType, Instance
from extyper.nodes import ArgKind
from extyper.solve import solve_constraints

class ArgumentInferContext(NamedTuple):
    """Type argument inference context.

    We need this because we pass around ``Mapping`` and ``Iterable`` types.
    These types are only known by ``TypeChecker`` itself.
    It is required for ``*`` and ``**`` argument inference.

    https://github.com/python/mypy/issues/11144
    """

    mapping_type: Instance
    iterable_type: Instance


def infer_function_type_arguments(callee_type: CallableType,
                                  arg_types: Sequence[Optional[Type]],
                                  arg_kinds: List[ArgKind],
                                  formal_to_actual: List[List[int]],
                                  context: ArgumentInferContext,
                                  strict: bool = True) -> List[Optional[Type]]:
    """Infer the type arguments of a generic function.

    Return an array of lower bound types for the type variables -1 (at
    index 0), -2 (at index 1), etc. A lower bound is None if a value
    could not be inferred.

    Arguments:
      callee_type: the target generic function
      arg_types: argument types at the call site (each optional; if None,
                 we are not considering this argument in the current pass)
      arg_kinds: nodes.ARG_* values for arg_types
      formal_to_actual: mapping from formal to actual variable indices
    """
    # Infer constraints.
    constraints = infer_constraints_for_callable(
        callee_type, arg_types, arg_kinds, formal_to_actual)

    # Solve constraints.
    type_vars = callee_type.type_var_ids()
    return solve_constraints(type_vars, constraints, strict)
# def infer_function_type_arguments(callee_type: CallableType,
#                                   arg_types: Sequence[Optional[Type]],
#                                   arg_kinds: List[ArgKind],
#                                   formal_to_actual: List[List[int]],

#                                   context: ArgumentInferContext,
#                                   strict: bool = True, maybe = False, args=None, only_constriaints=False) -> List[Optional[Type]]:
#     """Infer the type arguments of a generic function.

#     Return an array of lower bound types for the type variables -1 (at
#     index 0), -2 (at index 1), etc. A lower bound is None if a value
#     could not be inferred.

#     Arguments:
#       callee_type: the target generic function
#       arg_types: argument types at the call site (each optional; if None,
#                  we are not considering this argument in the current pass)
#       arg_kinds: nodes.ARG_* values for arg_types
#       formal_to_actual: mapping from formal to actual variable indices
#     """
#     if only_constriaints:
#         return infer_constraints_for_callable_pure(
#         callee_type, arg_types, arg_kinds, formal_to_actual)
#     # Infer constraints.
#     constraints, tv_at = infer_constraints_for_callable(
#         callee_type, arg_types, arg_kinds, formal_to_actual, args=args)
#     # Solve constraints.
#     type_vars = callee_type.type_var_ids()
#     return solve_constraints(type_vars, constraints, strict, maybe = maybe), tv_at


def infer_type_arguments(type_var_ids: List[TypeVarId],
                         template: Type, actual: Type,
                         is_supertype: bool = False) -> List[Optional[Type]]:
    # Like infer_function_type_arguments, but only match a single type
    # against a generic type.
    constraints = infer_constraints(template, actual,
                                    SUPERTYPE_OF if is_supertype else SUBTYPE_OF)
    return solve_constraints(type_var_ids, constraints)
