"""Type inference constraint solving"""

from typing import List, Dict, Optional
from collections import defaultdict

from extyper.types import Type, AnyType, UninhabitedType, TypeVarId, TypeOfAny, get_proper_type
from extyper.constraints import Constraint, SUPERTYPE_OF
from extyper.join import join_types
from extyper.meet import meet_types
from extyper.subtypes import is_subtype


def solve_constraints(vars: List[TypeVarId], constraints: List[Constraint],
                      strict: bool = True, maybe = False) -> List[Optional[Type]]:
    """Solve type constraints.

    Return the best type(s) for type variables; each type can be None if the value of the variable
    could not be solved.

    If a variable has no constraints, if strict=True then arbitrarily
    pick NoneType as the value of the type variable.  If strict=False,
    pick AnyType.
    """
    # Collect a list of constraints for each type variable.
    cmap: Dict[TypeVarId, List[Constraint]] = defaultdict(list)
    for con in constraints:
        cmap[con.type_var].append(con)

    res: List[Optional[Type]] = []

    # Solve each type variable separately.
    for tvar in vars:
        bottom: Optional[Type] = None
        top: Optional[Type] = None
        candidate: Optional[Type] = None
        maybe_candidates = []
        # Process each constraint separately, and calculate the lower and upper
        # bounds based on constraints. Note that we assume that the constraint
        # targets do not have constraint references.
        
        for i, c in enumerate(cmap.get(tvar, [])):
            # if i > 1000:
            #     break
            if maybe:
                if c.target not in maybe_candidates:
                    maybe_candidates.append(c.target)
            else:
                if c.op == SUPERTYPE_OF:
                    if bottom is None:
                        bottom = c.target
                    else:
                        bottom = join_types(bottom, c.target)
                else:
                    if top is None:
                        top = c.target
                    else:
                        top = meet_types(top, c.target) # wider

        top = get_proper_type(top)
        bottom = get_proper_type(bottom)
        if isinstance(top, AnyType) or isinstance(bottom, AnyType):
            source_any = top if isinstance(top, AnyType) else bottom
            assert isinstance(source_any, AnyType)
            res.append(AnyType(TypeOfAny.from_another_any, source_any=source_any))
            continue
        elif bottom is None and len(maybe_candidates) == 0:
            if top:
                candidate = top
            else:
                # No constraints for type variable -- 'UninhabitedType' is the most specific type.
                if strict:
                    candidate = UninhabitedType()
                    candidate.ambiguous = True
                else:
                    candidate = AnyType(TypeOfAny.special_form)
            maybe_candidates.append(candidate)
        elif top is None:
            candidate = bottom
        elif is_subtype(bottom, top):
            candidate = bottom
        else:
            candidate = None
        if maybe:
            res.append(maybe_candidates)
        else:
            res.append(candidate)
    return res
