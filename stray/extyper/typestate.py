"""
A shared state for all TypeInfos that holds global cache and dependency information,
and potentially other mutable TypeInfo state. This module contains mutable global state.
"""

from typing import Dict, Set, Tuple, Optional, List
from typing_extensions import ClassVar, Final

from extyper.nodes import TypeInfo
from extyper.types import Instance, TypeAliasType, get_proper_type, Type
from extyper import state

# Represents that the 'left' instance is a subtype of the 'right' instance
SubtypeRelationship = Tuple[Instance, Instance]

# A tuple encoding the specific conditions under which we performed the subtype check.
# (e.g. did we want a proper subtype? A regular subtype while ignoring variance?)
SubtypeKind = Tuple[bool, ...]

# A cache that keeps track of whether the given TypeInfo is a part of a particular
# subtype relationship
SubtypeCache = Dict[TypeInfo, Dict[SubtypeKind, Set[SubtypeRelationship]]]


class TypeState:
    """This class provides subtype caching to improve performance of subtype checks.
    It also holds protocol fine grained dependencies.

    Note: to avoid leaking global state, 'reset_all_subtype_caches()' should be called
    after a build has finished and after a daemon shutdown. This subtype cache only exists for
    performance reasons, resetting subtype caches for a class has no semantic effect.
    The protocol dependencies however are only stored here, and shouldn't be deleted unless
    not needed any more (e.g. during daemon shutdown).
    """
    # '_subtype_caches' keeps track of (subtype, supertype) pairs where supertypes are
    # instances of the given TypeInfo. The cache also keeps track of whether the check
    # was done in strict optional mode and of the specific *kind* of subtyping relationship,
    # which we represent as an arbitrary hashable tuple.
    # We need the caches, since subtype checks for structural types are very slow.
    _subtype_caches: Final[SubtypeCache] = {}

    # This contains protocol dependencies generated after running a full build,
    # or after an update. These dependencies are special because:
    #   * They are a global property of the program; i.e. some dependencies for imported
    #     classes can be generated in the importing modules.
    #   * Because of the above, they are serialized separately, after a full run,
    #     or a full update.
    # `proto_deps` can be None if after deserialization it turns out that they are
    # inconsistent with the other cache files (or an error occurred during deserialization).
    # A blocking error will be generated in this case, since we can't proceed safely.
    # For the description of kinds of protocol dependencies and corresponding examples,
    # see _snapshot_protocol_deps.
    proto_deps: ClassVar[Optional[Dict[str, Set[str]]]] = {}

    # Protocols (full names) a given class attempted to implement.
    # Used to calculate fine grained protocol dependencies and optimize protocol
    # subtype cache invalidation in fine grained mode. For example, if we pass a value
    # of type a.A to a function expecting something compatible with protocol p.P,
    # we'd have 'a.A' -> {'p.P', ...} in the map. This map is flushed after every incremental
    # update.
    _attempted_protocols: Final[Dict[str, Set[str]]] = {}
    # We also snapshot protocol members of the above protocols. For example, if we pass
    # a value of type a.A to a function expecting something compatible with Iterable, we'd have
    # 'a.A' -> {'__iter__', ...} in the map. This map is also flushed after every incremental
    # update. This map is needed to only generate dependencies like <a.A.__iter__> -> <a.A>
    # instead of a wildcard to avoid unnecessarily invalidating classes.
    _checked_against_members: Final[Dict[str, Set[str]]] = {}
    # TypeInfos that appeared as a left type (subtype) in a subtype check since latest
    # dependency snapshot update. This is an optimisation for fine grained mode; during a full
    # run we only take a dependency snapshot at the very end, so this set will contain all
    # subtype-checked TypeInfos. After a fine grained update however, we can gather only new
    # dependencies generated from (typically) few TypeInfos that were subtype-checked
    # (i.e. appeared as r.h.s. in an assignment or an argument in a function call in
    # a re-checked target) during the update.
    _rechecked_types: Final[Set[TypeInfo]] = set()

    # The two attributes below are assumption stacks for subtyping relationships between
    # recursive type aliases. Normally, one would pass type assumptions as an additional
    # arguments to is_subtype(), but this would mean updating dozens of related functions
    # threading this through all callsites (see also comment for TypeInfo.assuming).
    _assuming: Final[List[Tuple[TypeAliasType, TypeAliasType]]] = []
    _assuming_proper: Final[List[Tuple[TypeAliasType, TypeAliasType]]] = []
    # Ditto for inference of generic constraints against recursive type aliases.
    _inferring: Final[List[TypeAliasType]] = []

    # N.B: We do all of the accesses to these properties through
    # TypeState, instead of making these classmethods and accessing
    # via the cls parameter, since mypyc can optimize accesses to
    # Final attributes of a directly referenced type.

    @staticmethod
    def is_assumed_subtype(left: Type, right: Type) -> bool:
        for (l, r) in reversed(TypeState._assuming):
            if (get_proper_type(l) == get_proper_type(left)
                    and get_proper_type(r) == get_proper_type(right)):
                return True
        return False

    @staticmethod
    def is_assumed_proper_subtype(left: Type, right: Type) -> bool:
        for (l, r) in reversed(TypeState._assuming_proper):
            if (get_proper_type(l) == get_proper_type(left)
                    and get_proper_type(r) == get_proper_type(right)):
                return True
        return False

    @staticmethod
    def reset_all_subtype_caches() -> None:
        """Completely reset all known subtype caches."""
        TypeState._subtype_caches.clear()

    @staticmethod
    def reset_subtype_caches_for(info: TypeInfo) -> None:
        """Reset subtype caches (if any) for a given supertype TypeInfo."""
        if info in TypeState._subtype_caches:
            TypeState._subtype_caches[info].clear()

    @staticmethod
    def reset_all_subtype_caches_for(info: TypeInfo) -> None:
        """Reset subtype caches (if any) for a given supertype TypeInfo and its MRO."""
        for item in info.mro:
            TypeState.reset_subtype_caches_for(item)

    @staticmethod
    def is_cached_subtype_check(kind: SubtypeKind, left: Instance, right: Instance) -> bool:
        info = right.type
        if info not in TypeState._subtype_caches:
            return False
        cache = TypeState._subtype_caches[info]
        key = (state.strict_optional,) + kind
        if key not in cache:
            return False
        return (left, right) in cache[key]

    @staticmethod
    def record_subtype_cache_entry(kind: SubtypeKind,
                                   left: Instance, right: Instance) -> None:
        cache = TypeState._subtype_caches.setdefault(right.type, dict())
        cache.setdefault((state.strict_optional,) + kind, set()).add((left, right))

    @staticmethod
    def reset_protocol_deps() -> None:
        """Reset dependencies after a full run or before a daemon shutdown."""
        TypeState.proto_deps = {}
        TypeState._attempted_protocols.clear()
        TypeState._checked_against_members.clear()
        TypeState._rechecked_types.clear()

    @staticmethod
    def record_protocol_subtype_check(left_type: TypeInfo, right_type: TypeInfo) -> None:
        assert right_type.is_protocol
        TypeState._rechecked_types.add(left_type)
        TypeState._attempted_protocols.setdefault(
            left_type.fullname, set()).add(right_type.fullname)
        TypeState._checked_against_members.setdefault(
            left_type.fullname,
            set()).update(right_type.protocol_members)



def reset_global_state() -> None:
    """Reset most existing global state.

    Currently most of it is in this module. Few exceptions are strict optional status and
    and functools.lru_cache.
    """
    TypeState.reset_all_subtype_caches()
    TypeState.reset_protocol_deps()
