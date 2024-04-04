from itertools import chain


def get_typing_slots_in_query_dict(query_dict):
    return list(chain.from_iterable(
        map(
            lambda module_name: get_typing_slots_in_module_level_query_dict(module_name, query_dict[module_name]),
            query_dict.keys(),
        )
    ))


def get_typing_slots_in_module_level_query_dict(module_name, module_level_query_dict):
    return list(chain.from_iterable(
        map(
            lambda class_name: get_typing_slots_in_class_level_query_dict(module_name, class_name, module_level_query_dict[class_name]),
            module_level_query_dict.keys(),
        )
    ))


def get_typing_slots_in_class_level_query_dict(module_name, class_name, class_level_query_dict):
    return list(chain.from_iterable(
        map(
            lambda function_name: get_typing_slots_in_functional_level_query_dict(module_name, class_name, function_name, class_level_query_dict[function_name]),
            class_level_query_dict.keys(),
        )
    ))


def get_typing_slots_in_functional_level_query_dict(module_name, class_name, function_name, functional_level_query_dict):
    return list(map(
        lambda parameter_name: [module_name, class_name, function_name, parameter_name],
        functional_level_query_dict,
    ))
