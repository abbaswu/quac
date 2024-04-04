

class A:
    x:str


def f():
    a = A()
    setattr(a, "x", 1)

    return a.x