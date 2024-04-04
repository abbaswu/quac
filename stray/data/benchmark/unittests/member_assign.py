from typing import List

class A:
    x:int
    m:List[int]

    def f(self, y):
        # self.x = y
        self.m[0] = y
