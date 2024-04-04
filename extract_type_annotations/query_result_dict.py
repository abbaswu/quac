import logging

from collections import defaultdict

from typing import Callable, TypeAlias

from type_inference_result import TypeInferenceResult


# Query Dict
ClassLevelQueryDict: TypeAlias = dict[
    str,  # function_name
    list[
        str  # parameter_name_or_return
    ]
]

ModuleLevelQueryDict: TypeAlias = dict[
    str,  # class_name_or_global
    ClassLevelQueryDict
]

QueryDict: TypeAlias = dict[
    str,  # module_name
    ModuleLevelQueryDict
]


# Raw Result Defaultdict
FunctionLevelRawResultDefaultdict: TypeAlias = defaultdict[
    str,  # parameter_name_or_return
    list[
        str  # type_annotation_string
    ]
]

ClassLevelRawResultDefaultdict: TypeAlias = defaultdict[
    str,  # function_name
    FunctionLevelRawResultDefaultdict
]

ModuleLevelRawResultDefaultdict: TypeAlias = defaultdict[
    str,  # class_name_or_global
    ClassLevelRawResultDefaultdict
]

RawResultDefaultdict: TypeAlias = defaultdict[
    str,  # module_name
    ModuleLevelRawResultDefaultdict
]


# Raw Result Dict

FunctionLevelRawResultDict: TypeAlias = dict[
    str,  # parameter_name_or_return
    list[
        str  # type_annotation_string
    ]
]

ClassLevelRawResultDict: TypeAlias = dict[
    str,  # function_name
    FunctionLevelRawResultDict
]

ModuleLevelRawResultDict: TypeAlias = dict[
    str,  # class_name_or_global
    ClassLevelRawResultDict
]

RawResultDict: TypeAlias = dict[
    str,  # module_name
    ModuleLevelRawResultDict
]


def get_raw_result_defaultdict() -> RawResultDefaultdict:
    return RawResultDefaultdict(
        lambda: ModuleLevelRawResultDefaultdict(lambda: ClassLevelRawResultDefaultdict(lambda: FunctionLevelRawResultDefaultdict(list)))
    )


# Result Dict

FunctionLevelResultDict: TypeAlias = dict[
    str,  # parameter_name_or_return
    list[
        TypeInferenceResult  # type_annotation
    ]
]

ClassLevelResultDict: TypeAlias = dict[
    str,  # function_name
    FunctionLevelResultDict
]

ModuleLevelResultDict: TypeAlias = dict[
    str,  # class_name_or_global
    ClassLevelResultDict
]

ResultDict: TypeAlias = dict[
    str,  # module_name
    ModuleLevelResultDict
]


def generate_query_dict(
        module_name_to_file_path_dict: dict[str, str],
        module_name_to_function_name_to_parameter_name_list_dict: dict[str, dict[str, list[str]]],
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict: dict[str, dict[str, dict[str, list[str]]]]
) -> QueryDict:
    query_dict: QueryDict = dict()

    for module_name in module_name_to_file_path_dict:
        module_level_query_dict: ModuleLevelQueryDict = dict()

        class_name_or_global: str = 'global'
        class_level_query_dict: ClassLevelQueryDict = dict()

        for function_name, parameter_name_list in module_name_to_function_name_to_parameter_name_list_dict[
            module_name].items():
            class_level_query_dict[function_name] = parameter_name_list.copy()
            class_level_query_dict[function_name].append('return')

        if class_level_query_dict:
            module_level_query_dict[class_name_or_global] = class_level_query_dict

        for class_name, method_name_to_parameter_name_list_dict in \
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict[module_name].items():
            class_level_query_dict: ClassLevelQueryDict = dict()

            for method_name, parameter_name_list in method_name_to_parameter_name_list_dict.items():
                if parameter_name_list and parameter_name_list[0] in ('self', 'cls'):
                    class_level_query_dict[method_name] = parameter_name_list[1:].copy()
                else:
                    class_level_query_dict[method_name] = parameter_name_list.copy()
                class_level_query_dict[method_name].append('return')

            if class_level_query_dict:
                module_level_query_dict[class_name] = class_level_query_dict

        if module_level_query_dict:
            query_dict[module_name] = module_level_query_dict

    return query_dict


def raw_result_dict_from_query_dict_and_raw_result_defaultdict(
    query_dict: QueryDict,
    raw_result_defaultdict: RawResultDefaultdict
) -> RawResultDict:
    raw_result_dict: RawResultDict = dict()

    for module_name, module_level_query_dict in query_dict.items():
        module_level_raw_result_dict = raw_result_dict[module_name] = dict()

        for class_name_or_global, class_level_query_dict in module_level_query_dict.items():
            class_level_raw_result_dict = module_level_raw_result_dict[class_name_or_global] = dict()

            for function_name, function_level_query_dict in class_level_query_dict.items():
                function_level_raw_result_dict = class_level_raw_result_dict[function_name] = dict()

                for parameter_name_or_return in function_level_query_dict:
                    function_level_raw_result_dict[parameter_name_or_return] = raw_result_defaultdict[module_name][class_name_or_global][function_name][parameter_name_or_return]

    return raw_result_dict


def result_dict_from_raw_result_dict(
        raw_result_dict: RawResultDict,
        type_annotation_parser: Callable[[str, str], TypeInferenceResult]
) -> ResultDict:
    result_dict: ResultDict = dict()

    for module_name, module_level_raw_result_dict in raw_result_dict.items():
        module_level_result_dict = result_dict[module_name] = dict()

        for class_name_or_global, class_name_raw_result_dict in module_level_raw_result_dict.items():
            class_level_result_dict = module_level_result_dict[class_name_or_global] = dict()

            for function_name, function_level_raw_result_dict in class_name_raw_result_dict.items():
                function_level_result_dict = class_level_result_dict[function_name] = dict()

                for parameter_name_or_return, type_annotation_string_list in function_level_raw_result_dict.items():
                    type_annotation_list: list[TypeInferenceResult] = []
                    for type_annotation_string in type_annotation_string_list:
                        type_annotation = type_annotation_parser(
                            module_name,
                            type_annotation_string
                        )
                        type_annotation_list.append(type_annotation)

                        logging.info('Type annotation string %s parsed to %s', type_annotation_string, type_annotation)

                    function_level_result_dict[parameter_name_or_return] = type_annotation_list

    return result_dict


def raw_result_dict_from_result_dict(
    result_dict: ResultDict
) -> RawResultDict:
    raw_result_dict: RawResultDict = dict()

    for module_name, module_level_result_dict in result_dict.items():
        module_level_raw_result_dict = raw_result_dict[module_name] = dict()

        for class_name_or_global, class_name_result_dict in module_level_result_dict.items():
            class_level_raw_result_dict = module_level_raw_result_dict[class_name_or_global] = dict()

            for function_name, function_level_result_dict in class_name_result_dict.items():
                function_level_raw_result_dict = class_level_raw_result_dict[function_name] = dict()

                for parameter_name_or_return, type_annotation_list in function_level_result_dict.items():
                    type_annotation_string_list: list[str] = []

                    for type_annotation in type_annotation_list:
                        type_annotation_string_list.append(str(type_annotation))

                    function_level_raw_result_dict[parameter_name_or_return] = type_annotation_string_list

    return raw_result_dict
