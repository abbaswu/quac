import _ast
import argparse
import ast
import importlib
import json
import logging
import os
import sys
import typing
import types

import static_import_analysis
from parse_runtime_type_annotation import parse_runtime_type_annotation
from query_result_dict import get_raw_result_defaultdict
from unwrap import unwrap


def main():
    # Set up logging
    # https://stackoverflow.com/questions/10973362/python-logging-function-name-file-name-line-number-using-a-single-file
    FORMAT = '[%(asctime)s %(filename)s %(funcName)s():%(lineno)s]%(levelname)s: %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.INFO)

    # Parse command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--module-search-path', type=str, required=True,
                        help='Module search path, e.g. /tmp/module_search_path')
    parser.add_argument('-p', '--module-prefix', type=str, required=True,
                        help="Module prefix")
    parser.add_argument('-o', '--output-file', type=str, required=False,
                        default='output.json',
                        help='Output JSON file')
    args = parser.parse_args()

    module_search_absolute_path: str = os.path.abspath(args.module_search_path)
    module_prefix: str = args.module_prefix
    output_file: str = args.output_file

    # Find modules
    (
        module_name_to_file_path_dict,
        module_name_to_module_node_dict,
        module_name_to_function_name_to_parameter_name_list_dict,
        module_name_to_class_name_to_method_name_to_parameter_name_list_dict,
        module_name_to_import_tuple_set_dict,
        module_name_to_import_from_tuple_set_dict
    ) = static_import_analysis.do_static_import_analysis(module_search_absolute_path, module_prefix)

    # Import modules
    sys.path.insert(0, module_search_absolute_path)

    module_name_to_module = {}
    for module_name, file_path in module_name_to_file_path_dict.items():
        try:
            module_name_to_module[module_name] = importlib.import_module(module_name)
        except ImportError:
            logging.exception('Failed to import module %s', module_name)

    raw_result_defaultdict = get_raw_result_defaultdict()

    def handle_function(module_name: str, class_name_or_global: str, function_name: str, module: types.ModuleType, runtime_function: types.FunctionType):
        annotations = getattr(runtime_function, '__annotations__', dict())

        for parameter_name_or_return, runtime_type_annotation in annotations.items():
            try:
                type_annotation = parse_runtime_type_annotation(runtime_type_annotation, module)
                raw_result_defaultdict[module_name][class_name_or_global][function_name][parameter_name_or_return].append(str(type_annotation))
            except Exception as e:
                logging.exception('Cannot parse type annotation %s', runtime_type_annotation)

    for module_name, module in module_name_to_module.items():
        function_name_to_parameter_name_list_dict = module_name_to_function_name_to_parameter_name_list_dict.get(module_name, dict())
        for function_name, parameter_name_list_dict in function_name_to_parameter_name_list_dict.items():
            runtime_function = unwrap(module.__dict__.get(function_name, None))

            if not isinstance(runtime_function, types.FunctionType):
                logging.error(
                    'Cannot handle function %s in module %s',
                    function_name,
                    module_name
                )
                
                continue

            handle_function(module_name, 'global', function_name, module, runtime_function)
        
        class_name_to_method_name_to_parameter_name_list_dict = module_name_to_class_name_to_method_name_to_parameter_name_list_dict.get(module_name, dict())
        for class_name, method_name_to_parameter_name_list_dict in class_name_to_method_name_to_parameter_name_list_dict.items():
            runtime_class = module.__dict__.get(class_name, None)

            if not isinstance(module.__dict__[class_name], type):
                logging.error(
                    'Cannot handle class %s in module %s',
                    class_name,
                    module_name
                )

                continue
            
            for method_name, parameter_name_list in method_name_to_parameter_name_list_dict.items():
                runtime_method = unwrap(runtime_class.__dict__.get(method_name, None))

                if not isinstance(runtime_method, types.FunctionType):
                    logging.error(
                            'Cannot handle method %s in class %s in module %s',
                            method_name,
                            class_name,
                            module_name
                    )

                    continue

                handle_function(module_name, class_name, method_name, module, runtime_method)

    with open(output_file, 'w') as output_file_io:
        json.dump(raw_result_defaultdict, output_file_io, indent=4)


if __name__ == '__main__':
    main()
