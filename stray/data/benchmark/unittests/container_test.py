from typing import List, Tuple, Set


class A:
    x:List[Tuple[str,str]]

    def f(self, e1, e2):
        self.x.append((e1, e2))

        