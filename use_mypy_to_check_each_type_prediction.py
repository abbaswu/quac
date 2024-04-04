import argparse
import ast
import copy
import difflib
import json
import logging
import os
import os.path
import re
import subprocess
import typing

import pandas as pd

from copy_directory import copy_directory
from generate_ast_arg import generate_ast_arg
from module_name_from_module_search_path_and_python_file_path import module_name_from_module_search_path_and_python_file_path
from static_import_analysis import do_static_import_analysis
from strip_type_annotations import strip_type_annotations
from type_inference_result import iterate_type_inference_classes
from parse_type_inference_result import parse


MYPY_OUTPUT_LINE_PATTERN: re.Pattern = re.compile(r'([^:]+):(\d+): error: (.+) \[([^\]]+)\]$')
MYPY_COMMAND_LINE_OPTIONS: list[str] = [
    '--check-untyped-defs',
    '--no-warn-no-return',
    '--no-strict-optional',
    '--disable-error-code', 'override',
    '--disable-error-code', 'assignment',
    '--disable-error-code', 'has-type',
    '--disable-error-code', 'import',
    '--disable-error-code', 'var-annotated',
    '--disable-error-code', 'no-untyped-def',
    '--disable-error-code', 'no-redef',
    '--disable-error-code', 'misc',
    '--disable-error-code', 'name-defined',
    '--disable-error-code', 'call-arg',
    '--disable-error-code', 'no-untyped-call',
]

class ManagedWorkingDirectory:
    def __init__(self, path: str):
        self.path = path
        self.original_path = None

    def __enter__(self):
        # Save the current working directory
        self.original_path = os.getcwd()

        # Change to the specified directory
        os.chdir(self.path)

        return self

    def __exit__(self, exc_type, exc_value, traceback):
        # Restore the original working directory
        if self.original_path:
            os.chdir(self.original_path)


def parse_mypy_output_lines(
    mypy_output_lines: typing.Iterable[str],
    module_search_path: str
) -> pd.DataFrame:
    rows: list[tuple[str, int, str, str]] = []

    for mypy_output_line in mypy_output_lines:
        match: re.Match | None = MYPY_OUTPUT_LINE_PATTERN.match(mypy_output_line)
        if match is not None:
            relative_file_path, line_number_string, error_message, error_type = match.groups()

            file_path = os.path.join(module_search_path, relative_file_path)
            module_name = module_name_from_module_search_path_and_python_file_path(module_search_path, file_path)

            line_number = int(line_number_string)

            rows.append((module_name, line_number, error_message, error_type))

    return pd.DataFrame(rows, columns=['module_name', 'line_number', 'error_message', 'error_type'])


def run_mypy_and_parse_output(
    module_search_path: str,
    module_names: typing.Iterable[str],
    run_command_in_environment_prefix: list[str],
) -> pd.DataFrame:
    with ManagedWorkingDirectory(module_search_path):
        mypy_module_option_string = []
        for module_name in module_names:
            mypy_module_option_string.append('-m')
            mypy_module_option_string.append(module_name)
        
        result = subprocess.run(
            run_command_in_environment_prefix + ['mypy'] + MYPY_COMMAND_LINE_OPTIONS + mypy_module_option_string,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )

        stderr = result.stderr.decode()

        print(stderr)

        # Parse mypy's output lines
        mypy_output_dataframe: pd.DataFrame = parse_mypy_output_lines(
            result.stdout.decode().splitlines(),
            module_search_path
        )

        return mypy_output_dataframe


def add_type_annotation(
    module_node: ast.Module,
    module_name: str,
    class_name_or_global: str,
    function_name: str,
    parameter_name_or_return: str,
    type_annotation
):
    if class_name_or_global == 'global':
        class_node = module_node
    else:
        class_nodes = [
            child for child in module_node.body
            if isinstance(child, ast.ClassDef)
            and child.name == class_name_or_global
        ]

        if not class_nodes:
            return

        class_node = class_nodes[0]

    function_nodes = [
        child
        for child in class_node.body
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
        and child.name == function_name
    ]

    if not function_nodes:
        return

    # Retrieve the last definition
    # https://peps.python.org/pep-0484/#function-method-overloading
    function_node = function_nodes[-1]


    if parameter_name_or_return == 'return':
        function_node.returns = ast.Constant(str(type_annotation))
    else:
        parameter_names_to_args = {
            arg.arg: arg
            for arg in generate_ast_arg(function_node)
        }

        if parameter_name_or_return not in parameter_names_to_args:
            return

        arg = parameter_names_to_args[parameter_name_or_return]

        arg.annotation = ast.Constant(type_annotation.string_representation_in_module(module_name))


def find_indices_of_new_rows(
    original_rows: list[tuple[typing.Hashable, ...]],
    new_rows: list[tuple[typing.Hashable, ...]]
) -> list[int]:
    matcher = difflib.SequenceMatcher(
        None,
        original_rows,
        new_rows
    )
    
    opcodes = matcher.get_opcodes()

    indices_of_new_rows = []
    for (
        tag,
        start_index_in_first_list,
        end_index_in_first_list,
        start_index_in_second_list,
        end_index_in_second_list
    ) in opcodes:
        if tag == 'insert':
            indices_of_new_rows.extend(range(start_index_in_second_list, end_index_in_second_list))
    
    return indices_of_new_rows


def diff_mypy_output_dataframe(
    old_mypy_output_dataframe: pd.DataFrame,
    new_mypy_output_dataframe: pd.DataFrame
) -> pd.DataFrame:
    rows_in_old_mypy_output_dataframe = [
        t[1:]  # Skip the index element
        for t in old_mypy_output_dataframe.itertuples()
    ]

    rows_in_new_mypy_output_dataframe = [
        t[1:]  # Skip the index element
        for t in new_mypy_output_dataframe.itertuples()
    ]

    indices_of_new_rows = find_indices_of_new_rows(
        rows_in_old_mypy_output_dataframe,
        rows_in_new_mypy_output_dataframe
    )

    # Use .iloc to select rows based on the indices
    return new_mypy_output_dataframe.iloc[indices_of_new_rows].copy()


def check_each_type_prediction(
    module_search_path: str,
    module_name_to_module_node_without_type_annotation_dict: typing.Mapping[str, ast.Module],
    module_name_to_module_path_dict: typing.Mapping[str, str],
    result_dict,
    run_command_in_environment_prefix: list[str]
):
    """Returns a pd.DataFrame with the following rows:
    line_number
    module_name
    error_message
    error_type
    type_annotation
    type_annotation_module_name
    type_annotation_class_name_or_global
    type_annotation_function_name
    type_annotation_parameter_name_or_return"""
    dataframe_fragments = [
        pd.DataFrame(
            {
                'line_number': [],
                'module_name': [],
                'error_message': [],
                'error_type': [],
                'type_annotation': [],
                'type_annotation_module_name': [],
                'type_annotation_class_name_or_global': [],
                'type_annotation_function_name': [],
                'type_annotation_parameter_name_or_return': []
            }
        )
    ]

    number_of_type_predictions = 0

    # Add all imports to the module nodes
    module_name_to_module_node_with_imports_dict = {}
    for module_name, module_level_result_dict in result_dict.items():
        module_node_copy = copy.deepcopy(module_name_to_module_node_without_type_annotation_dict[module_name])
        module_name_to_import_set = set()

        for class_name_or_global, class_level_result_dict in module_level_result_dict.items():
            for function_name, function_level_result_dict in class_level_result_dict.items():
                for parameter_name_or_return, type_annotation_list in function_level_result_dict.items():
                    number_of_type_predictions += 1

                    for type_annotation in type_annotation_list:
                        for type_inference_class in iterate_type_inference_classes(
                            type_annotation
                        ):
                            type_inference_class_module_name: str | None = type_inference_class.module_name
                            if type_inference_class_module_name and type_inference_class_module_name != module_name: # No self-imports
                                module_name_to_import_set.add(type_inference_class_module_name)
        
        if module_name_to_import_set:
            statements_to_add = []

            # Add "import typing"
            import_typing = ast.Import(names=[ast.alias(name='typing', asname=None)])
            statements_to_add.append(import_typing)

            # Add "if typing.TYPE_CHECKING: import ..." after that
            type_checking_import = ast.If(
                test=ast.Attribute(
                    value=ast.Name(id='typing', ctx=ast.Load()),
                    attr='TYPE_CHECKING',
                    ctx=ast.Load()
                ),
                body=[
                    ast.Import(names=[ast.alias(name=module_name_to_import, asname=None)])
                    for module_name_to_import in module_name_to_import_set
                ],
                orelse=[]
            )
            statements_to_add.append(type_checking_import)

            module_node_copy.body[0:0] = statements_to_add

        # Make sure to fix locations in the AST
        module_name_to_module_node_with_imports_dict[module_name] = ast.fix_missing_locations(module_node_copy)

    # Save the module nodes
    for module_name, module_node_with_imports in module_name_to_module_node_with_imports_dict.items():
        module_path = module_name_to_module_path_dict[module_name]

        with open(module_path, 'w') as fp:
            fp.write(ast.unparse(module_node_with_imports))

    # Install from requirements.txt
    requirements_txt_path = os.path.join(module_search_path, 'requirements.txt')
    if os.path.isfile(requirements_txt_path):
        result = subprocess.run(
            run_command_in_environment_prefix + [
                'pip',
                'install',
                '-r',
                requirements_txt_path
            ]
        )

        # If the script returned a non-zero exit code, raise an exception
        if result.returncode != 0:
            raise Exception(f"Script returned non-zero exit code {result.returncode}.")

    # Run Mypy
    mypy_output_dataframe = run_mypy_and_parse_output(
        module_search_path,
        module_name_to_module_node_without_type_annotation_dict.keys(),
        run_command_in_environment_prefix
    )

    # Add each type annotation to the revelant module
    type_prediction_counter = 0

    for module_name, module_level_result_dict in result_dict.items():
        module_node_with_imports = module_name_to_module_node_with_imports_dict[module_name]
        module_path = module_name_to_module_path_dict[module_name]

        for class_name_or_global, class_level_result_dict in module_level_result_dict.items():
            for function_name, function_level_result_dict in class_level_result_dict.items():
                for parameter_name_or_return, type_annotation_list in function_level_result_dict.items():
                    type_prediction_counter += 1

                    print(f'Type prediction counter: {type_prediction_counter} / {number_of_type_predictions}')
                    if type_annotation_list:
                        top_type_annotation = type_annotation_list[0]

                        module_node_with_imports_copy = copy.deepcopy(module_node_with_imports)

                        add_type_annotation(
                            module_node_with_imports_copy,
                            module_name,
                            class_name_or_global,
                            function_name,
                            parameter_name_or_return,
                            top_type_annotation
                        )

                        # Save the modified module node
                        with open(module_path, 'w') as fp:
                            fp.write(ast.unparse(module_node_with_imports_copy))
                        
                        # Run mypy
                        mypy_output_dataframe_ = run_mypy_and_parse_output(
                            module_search_path,
                            module_name_to_module_node_without_type_annotation_dict.keys(),
                            run_command_in_environment_prefix
                        )

                        # Calculate diff
                        diff = diff_mypy_output_dataframe(
                            mypy_output_dataframe,
                            mypy_output_dataframe_
                        )

                        # Initialize a new column with a single string value
                        diff['type_annotation'] = str(top_type_annotation)
                        diff['type_annotation_module_name'] = module_name
                        diff['type_annotation_class_name_or_global'] = class_name_or_global
                        diff['type_annotation_function_name'] = function_name
                        diff['type_annotation_parameter_name_or_return'] = parameter_name_or_return

                        dataframe_fragments.append(diff)             
        
        # Resave the original module node
        with open(module_path, 'w') as fp:
            fp.write(ast.unparse(module_node_with_imports))

    return pd.concat(dataframe_fragments)


def read_result_dict_from_output_json_file(output_json_file_path):
    with open(output_json_file_path, 'r') as fp:
        output = json.load(fp)

    parsed = {}

    for m, md in output.items():
        for c, cd in md.items():
            for f, fd in cd.items():
                for p in fd:
                    ts = fd[p]

                    parsed_ts = []
                    for t in ts:
                        try:
                            parsed_ts.append(parse(t))
                        except:
                            logging.exception('Failed to parse type annotation %s', t)

                    parsed.setdefault(
                        m, {}
                    ).setdefault(
                        c, {}
                    ).setdefault(
                        f, {}
                    )[p] = parsed_ts

    return parsed


def use_mypy_to_check_each_type_prediction(
    module_search_path: str,
    module_prefix: str,
    type_predictions_json_path: str,
    output_directory_path: str,
    output_csv_path: str,
    run_mypy_prefix: list[str],
):
    # Read type predictions
    result_dict = read_result_dict_from_output_json_file(type_predictions_json_path)

    # Copy directory
    copy_directory(
        module_search_path,
        output_directory_path
    )

    # Strip type annotations
    strip_type_annotations(output_directory_path)

    # Do static import analysis
    module_name_to_module_path_dict, *_ = do_static_import_analysis(output_directory_path, module_prefix)

    module_name_to_module_node_without_type_annotation_dict = {}
    for module_name, module_path in module_name_to_module_path_dict.items():
        with open(module_path, 'r') as fp:
            module_node = ast.parse(fp.read())
            module_name_to_module_node_without_type_annotation_dict[module_name] = module_node
    
    # Check each type prediction
    df = check_each_type_prediction(
        output_directory_path,
        module_name_to_module_node_without_type_annotation_dict,
        module_name_to_module_path_dict,
        result_dict,
        run_mypy_prefix
    )

    # Save result 
    df.to_csv(output_csv_path, index=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--module-search-path', type=str, required=True)
    parser.add_argument('--module-prefix', type=str, required=True)
    parser.add_argument('--type-predictions-json-path', type=str, required=True)
    parser.add_argument('--output-directory-path', type=str, required=True)
    parser.add_argument('--output-csv-path', type=str, required=True)
    parser.add_argument('--run-mypy-prefix', type=str, required=True)
    args = parser.parse_args()

    use_mypy_to_check_each_type_prediction(
            args.module_search_path,
            args.module_prefix,
            args.type_predictions_json_path,
            args.output_directory_path,
            args.output_csv_path,
            args.run_mypy_prefix.split(),
    )

