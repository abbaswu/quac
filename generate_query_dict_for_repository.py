import argparse
import json
import logging
import os.path

from query_result_dict import QueryDict, ResultDict, generate_query_dict, raw_result_dict_from_result_dict
from static_import_analysis import do_static_import_analysis


def generate_query_dict_for_repository(
        module_search_path,
        module_prefix
):
    # Do static import analysis
    (
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict,
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict
    ) = do_static_import_analysis(module_search_path, module_prefix)
    
    module_list: list[str] = list(module_name_to_file_path_dict.keys())

    # Generate query dict
    query_dict: QueryDict = generate_query_dict(
        module_name_to_file_path_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict
    )

    return query_dict


if __name__ == '__main__':
    # Set up logging
    FORMAT = '%(asctime)s %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.INFO)

    # Parse command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--module-search-path', type=str, required=True)
    parser.add_argument('-p', '--module-prefix', type=str, required=True)
    parser.add_argument('-o', '--output-query-dict', type=str, required=True)
    args = parser.parse_args()

    module_search_path: str = args.module_search_path
    module_prefix: str = args.module_prefix
    output_query_dict = args.output_query_dict

    # Generate query dict
    query_dict = generate_query_dict_for_repository(
            module_search_path,
            module_prefix
    )

    with open(output_query_dict, 'w') as fp:
        json.dump(query_dict, fp, indent=4)

