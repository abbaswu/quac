from type_definitions import RuntimeClass


def get_comprehensive_dict_for_runtime_class(
        runtime_class: RuntimeClass
) -> dict[str, object]:
    comprehensive_dict: dict[str, object] = dict()

    # Consider all the classes within the class's MRO.
    for mro_class in reversed(runtime_class.__mro__):
        comprehensive_dict.update(mro_class.__dict__)

    return comprehensive_dict
