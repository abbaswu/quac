from type_definitions import RuntimeClass, UnwrappedRuntimeFunction
from unwrap import unwrap


def get_unwrapped_constructor(runtime_class: RuntimeClass) -> UnwrappedRuntimeFunction:
    """
    Get unwrapped constructor.

    Lookup order:
    - __init__ in current type
    - __new__ in current type
    - __init__ in next type in __mro__
    - __new__ in next type in __mro__
    - ...
    """

    for mro_class in runtime_class.__mro__:
        for method_name in ('__init__', '__new__'):
            if method_name in mro_class.__dict__:
                unwrapped_constructor = unwrap(mro_class.__dict__[method_name])
                if isinstance(unwrapped_constructor, UnwrappedRuntimeFunction):
                    return unwrapped_constructor

    assert False
