def unwrap(o: object) -> object:
    if callable(o) and hasattr(o, '__wrapped__'):
        return getattr(o, '__wrapped__')
    else:
        return o
