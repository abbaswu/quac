from typing import Dict, Sequence, Optional, Callable

import extyper.subtypes
import extyper.sametypes
from extyper.expandtype import expand_type
from extyper.types import (
    Type, TypeVarId, TypeVarType, CallableType, AnyType, PartialType, get_proper_types,
    TypeVarLikeType, ProperType, ParamSpecType
)
from extyper.nodes import Context


def get_target_type(
    tvar: TypeVarLikeType,
    type: ProperType,
    callable: CallableType,
    report_incompatible_typevar_value: Callable[[CallableType, Type, str, Context], None],
    context: Context,
    skip_unsatisfied: bool
) -> Optional[Type]:
    # TODO(shantanu): fix for ParamSpecType
    if isinstance(tvar, ParamSpecType):
        return None
    assert isinstance(tvar, TypeVarType)
    values = get_proper_types(tvar.values)
    if values:
        if isinstance(type, AnyType):
            return type
        if isinstance(type, TypeVarType) and type.values:
            # Allow substituting T1 for T if every allowed value of T1
            # is also a legal value of T.
            if all(any(extyper.sametypes.is_same_type(v, v1) for v in values)
                   for v1 in type.values):
                return type
        matching = []
        for value in values:
            if extyper.subtypes.is_subtype(type, value):
                matching.append(value)
        if matching:
            best = matching[0]
            # If there are more than one matching value, we select the narrowest
            for match in matching[1:]:
                if extyper.subtypes.is_subtype(match, best):
                    best = match
            return best
        if skip_unsatisfied:
            return None
        report_incompatible_typevar_value(callable, type, tvar.name, context)
    else:
        upper_bound = tvar.upper_bound
        if not extyper.subtypes.is_subtype(type, upper_bound):
            if skip_unsatisfied:
                return None
            report_incompatible_typevar_value(callable, type, tvar.name, context)
    return type


def apply_generic_arguments(
        callable: CallableType, orig_types: Sequence[Optional[Type]],
        report_incompatible_typevar_value: Callable[[CallableType, Type, str, Context], None],
        context: Context,
        skip_unsatisfied: bool = False, fail=False) -> CallableType:
    """Apply generic type arguments to a callable type.

    For example, applying [int] to 'def [T] (T) -> T' results in
    'def (int) -> int'.

    Note that each type can be None; in this case, it will not be applied.

    If `skip_unsatisfied` is True, then just skip the types that don't satisfy type variable
    bound or constraints, instead of giving an error.
    """
    tvars = callable.variables
    assert len(tvars) == len(orig_types)
    # Check that inferred type variable values are compatible with allowed
    # values and bounds.  Also, promote subtype values to allowed values.
    types = get_proper_types(orig_types)

    # Create a map from type variable id to target type.
    id_to_type: Dict[TypeVarId, Type] = {}

    for tvar, type in zip(tvars, types):
        if isinstance(type, PartialType):
            type = AnyType(0)
        assert not isinstance(type, PartialType), "Internal error: must never apply partial type"
        if type is None:
            continue

        target_type = get_target_type(
            tvar, type, callable, report_incompatible_typevar_value, context, skip_unsatisfied
        )
        if target_type is not None:
            id_to_type[tvar.id] = target_type
        elif fail:
            return None

    # Apply arguments to argument types.
    arg_types = [expand_type(at, id_to_type) for at in callable.arg_types]

    # The callable may retain some type vars if only some were applied.
    remaining_tvars = [tv for tv in tvars if tv.id not in id_to_type]

    return callable.copy_modified(
        arg_types=arg_types,
        ret_type=expand_type(callable.ret_type, id_to_type),
        variables=remaining_tvars,
    )
