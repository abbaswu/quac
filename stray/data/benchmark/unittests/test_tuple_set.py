from typing import Tuple, Set
class A:
    ts:Set[Tuple[int,int]]


    def f(self, a,b):
        self.ts.add((a, b))

