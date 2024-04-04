
class A:
    x:int
    def __init__(self) -> None:
        pass


def f(klass):
    return klass()


def g():
    return f(A)
