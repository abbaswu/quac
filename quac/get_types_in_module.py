import logging
from types import ModuleType


def get_types_in_module(module: ModuleType) -> set[type]:
    types_in_module: set[type] = set()
    keys = dir(module)
    for key in keys:
        try:
            value = getattr(module, key)
            if isinstance(value, type):
                types_in_module.add(value)
        except Exception:
            logging.exception('Failed to get %s in %s', key, module)

    return types_in_module
