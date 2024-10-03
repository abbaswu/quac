IGNORED_ATTRIBUTES = {
    # https://peps.python.org/pep-3119/
    # https://github.com/python/cpython/blob/main/Modules/_abc.c
    '__abstractmethods__',
    '_abc_impl',
    # https://peps.python.org/pep-0544/
    '_is_protocol',
    '_is_runtime_protocol',
    # https://peps.python.org/pep-0560/
    '__class_getitem__',
    '__orig_bases__',
    # https://docs.python.org/3/reference/datamodel.html#custom-classes
    '__name__',
    '__module__',
    '__dict__',
    '__weakref__',
    '__bases__',
    '__doc__',
    '__annotations__',
    '__type_params__',
    # https://docs.python.org/3/reference/datamodel.html#slots
    '__slots__',
    # https://peps.python.org/pep-0585/
    '__parameters__',
    # https://docs.python.org/3/library/pickle.html
    '__getstate__',
    '__setstate__',
    # https://docs.python.org/3/reference/datamodel.html#object.__length_hint__
    # This method is purely an optimization and is never required for correctness.
    '__length_hint__',
    # Any object is convertible to bool in Python, and __bool__ only customizes that.
    '__bool__'
} | {
    # all attributes in the Typeshed definition of `object`
    '__ne__',
    '__reduce__',
    '__setattr__',
    '__eq__',
    '__doc__',
    '__lt__',
    '__class__',
    '__gt__',
    '__module__',
    '__le__',
    '__repr__',
    '__dict__',
    '__sizeof__',
    '__init__',
    '__str__',
    '__dir__',
    '__getattribute__',
    '__format__',
    '__delattr__',
    '__init_subclass__',
    '__ge__',
    '__subclasshook__',
    '__hash__',
    '__reduce_ex__',
    '__new__',
    '__annotations__'
} | {
    # https://docs.python.org/3/library/stdtypes.html#special-attributes
    # The implementation adds a few special read-only attributes to several object types, where they are relevant.
    # Some of these are not reported by the dir() built-in function.
    '__dict__',
    '__class__',
    '__bases__',
    '__name__',
    '__qualname__',
    '__type_params__',
    '__mro__',
    'mro',
    '__subclasses__'
}
