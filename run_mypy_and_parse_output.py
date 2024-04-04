import json
import os.path
import re
import sys
import subprocess

from typing import Iterable

import pandas as pd

from module_name_from_module_search_path_and_python_file_path import module_name_from_module_search_path_and_python_file_path


mypy_output_line_pattern: re.Pattern = re.compile('([^:]+):(\d+): error: (.+) \[([^\]]+)\]$')


def parse_mypy_output_lines(
    mypy_output_lines: Iterable[str],
    module_search_path: str
) -> pd.DataFrame:
    rows: list[tuple[str, int, str, str]] = []

    for mypy_output_line in mypy_output_lines:
        match: re.Match | None = mypy_output_line_pattern.match(mypy_output_line)
        if match is not None:
            relative_file_path, line_number_string, error_message, error_type = match.groups()

            file_path = os.path.join(module_search_path, relative_file_path)
            module_name = module_name_from_module_search_path_and_python_file_path(module_search_path, file_path)

            line_number = int(line_number_string)

            rows.append((module_name, line_number, error_message, error_type))

    return pd.DataFrame(rows, columns=['module_name', 'line_number', 'error_message', 'error_type'])


def run_mypy_and_parse_output(
    module_search_path: str,
    module_list: list[str]
) -> pd.DataFrame:
    result = subprocess.run(
        [
            'bash',
            'run_mypy.sh',
            '-s',
            module_search_path,
            '-l',
            json.dumps(module_list)
        ], 
        stdout=subprocess.PIPE
    )

    # If the script returned a non-zero exit code, raise an exception
    if result.returncode != 0:
        raise Exception(f"Script returned non-zero exit code {result.returncode}.")

    # Parse mypy's output lines
    mypy_output_dataframe: pd.DataFrame = parse_mypy_output_lines(
        result.stdout.decode().splitlines(),
        module_search_path
    )

    return mypy_output_dataframe

