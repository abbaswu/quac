"""
Relations among type variables.
"""
import ast
import typing
from collections import defaultdict
from enum import Enum, auto

import networkx as nx


class RelationType(Enum):
    KeyOf = auto()
    ValueOf = auto()
    IterTargetOf = auto()
    ElementOf = auto()
    ParameterOf = auto()
    ReturnValueOf = auto()    
    SendTargetOf = auto()
    YieldFromAwaitResultOf = auto()


RelationTypeAndParameter = tuple[RelationType, typing.Optional[object]]
