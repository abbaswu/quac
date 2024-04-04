import abc
class A(abc.ABC):
    pass
class B(metaclass=abc.ABCMeta):
    pass
