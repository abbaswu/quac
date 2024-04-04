from collections import defaultdict

from query_or_result_dict import QueryOrResultDict


def result_dict_from_query_dict_and_prelimary_result_dict(
    query_dict: QueryOrResultDict,
    prelimary_result_dict: defaultdict[
        str, # module_name
        defaultdict[
            str, # class_name_or_global
            defaultdict[
                str, # function_name
                defaultdict[
                    str, # parameter_name_or_return
                    # TODO: structured type annotations
                    list[
                        str # type_annotation_string
                    ] 
                ]
            ]
        ]
    ]
) -> QueryOrResultDict:
    result_dict: QueryOrResultDict = dict()

    for module_name, module_level_query_dict in query_dict.items():
        module_level_result_dict = result_dict[module_name] = dict()

        for class_name_or_global, class_level_query_dict in module_level_query_dict.items():
            class_level_result_dict = module_level_result_dict[class_name_or_global] = dict()

            for function_name, function_level_query_dict in class_level_query_dict.items():
                function_level_result_dict = class_level_result_dict[function_name] = dict()

                for parameter_name_or_return in function_level_query_dict:
                    function_level_result_dict[parameter_name_or_return] = prelimary_result_dict[module_name][class_name_or_global][function_name][parameter_name_or_return]

    return result_dict
