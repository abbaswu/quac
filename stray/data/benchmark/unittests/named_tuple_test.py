from collections import namedtuple
from typing import NamedTuple


class A(NamedTuple):
    x:int


def f(x):
    return x.x

a = A(1)

f(a)
