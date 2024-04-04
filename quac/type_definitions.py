import ast
import types
import typing


# Module
Module = types.ModuleType

# Class
RuntimeClass = type

Class = RuntimeClass

# Unwrapped Runtime Function
# Unwrap decorated functions (staticmethod, functools._lru_cache_wrapper, etc.) through the `__wrapped__` attribute
# Based on https://stackoverflow.com/questions/1166118/how-to-strip-decorators-from-a-function-in-python
UnwrappedRuntimeFunction = typing.Union[
    types.FunctionType,
    types.BuiltinFunctionType,
    types.WrapperDescriptorType,
    types.MethodDescriptorType,
    types.ClassMethodDescriptorType
]

NamedFunctionDefinition = typing.Union[
    ast.FunctionDef,
    ast.AsyncFunctionDef
]

FunctionDefinition = typing.Union[
    NamedFunctionDefinition,
    ast.Lambda
]

Function = typing.Union[
    UnwrappedRuntimeFunction,
    FunctionDefinition
]

class UnboundMethod:
    __slots__ = ('class_', 'function')
    
    def __init__(self, class_: Class, function: Function):
        self.class_ = class_
        self.function = function

    def __hash__(self) -> int:
        return hash((self.class_, self.function))

    def __repr__(self):
        return f'UnboundMethod({self.class_}, {self.function})'
    
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, UnboundMethod):
            return False
        return self.class_ == other.class_ and self.function == other.function


class Instance:
    __slots__ = ('class_',)
    
    def __init__(self, class_: Class):
        self.class_ = class_
    
    def __hash__(self) -> int:
        return hash(self.class_)

    def __repr__(self):
        return f'Instance({self.class_})'
    
    def __eq__(self, other: object) -> int:
        if not isinstance(other, Instance):
            return False
        return self.class_ == other.class_


class BoundMethod:
    __slots__ = ('instance', 'function')
    
    def __init__(self, instance: Instance, function: Function):
        self.instance = instance
        self.function = function
    
    def __hash__(self) -> int:
        return hash((self.instance, self.function))

    def __repr__(self):
        return f'BoundMethod({self.instance}, {self.function})'
    
    def __eq__(self, other: object) -> bool:
        if not isinstance(other, BoundMethod):
            return False
        return self.instance == other.instance and self.function == other.function


RuntimeTerm = typing.Union[
    Module,
    Class,
    Function,
    UnboundMethod,
    Instance,
    BoundMethod
]


# An apparent UnwrappedRuntimeFunction could actually be something else logically
def runtime_term_of_unwrapped_runtime_function(
    unwrapped_runtime_function: UnwrappedRuntimeFunction
):
    if isinstance(unwrapped_runtime_function, types.BuiltinMethodType):
        __self__ = unwrapped_runtime_function.__self__
        # If __self__ is not a module
        # Then runtime_term is actually a METHOD
        if not isinstance(__self__, types.ModuleType):
            return BoundMethod(Instance(type(__self__)), unwrapped_runtime_function)
        else:
            return unwrapped_runtime_function
    else:
        return unwrapped_runtime_function
