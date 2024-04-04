from typing import Union

class A:
    x:int
    def f(self, x):
        self.x = x


class B:
    x:str
    def f(self, x):
        self.x = x


class C(A, B):
    x:Union[int,str]
    def f(self, x):
        self.x = x


af = A.f
bf = B.f
cf = C.f

ax = A().x
bx = B().x
cx = C().x

"""Methods must satisfy covariance/contravariance of args/return"""
# af := Callable[[A, int], None]
# bf := Callable[[B, str], None]
# cf := Callable[[C, object], None]

"""All attributes should have the same type in all classes"""
# ax := object
# bx := object
# cx := object