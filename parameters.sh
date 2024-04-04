# MUST NOT end with a '/', otherwise breaks hityper

MOUNTED_MODULE_SEARCH_PATH='/mnt/mounted_module_search_path'

LOCAL_MODULE_SEARCH_PATH='/root/local_module_search_path'

OUTPUT_PATH='/mnt/output_path'
QUERY_DICT_JSON="${OUTPUT_PATH}/query_dict.json"
OUTPUT_JSON="${OUTPUT_PATH}/output.json"
TIME_OUTPUT_JSON="${OUTPUT_PATH}/time_output.json"
TYPE_CHECKING_OUTPUT_CSV="${OUTPUT_PATH}/use_mypy_to_check_each_type_prediction.csv"
TYPE_CHECKING_OUTPUT_DIRECTORY="${OUTPUT_PATH}/repository_for_type_checking"
RAW_OUTPUT_DIRECTORY="${OUTPUT_PATH}/raw_output_directory"

IS_PORT_IN_USE='/root/is_port_in_use.py'
GENERATE_QUERY_DICT_FOR_REPOSITORY='/root/generate_query_dict_for_repository.py'
STRIP_TYPE_ANNOTATIONS='/root/strip_type_annotations.py'
VERIFY_QUERY_DICT='/root/verify_query_dict.py'
PRINT_PYTHON_FILE_PATHS='/root/print_python_file_paths.py'

# Stray-related
RUN_STRAY='/root/run_stray.sh'
STRAY_ROOT='/root/stray'
PARSE_STRAY_RESULT_DIRECTORY='/root/parse_stray_result_directory.py'

# HiTyper-related

RUN_HITYPER='/root/run_hityper.sh'
PARSE_HITYPER_OUTPUT_DIRECTORY='/root/parse_hityper_output_directory.py'

# QuAC-related

QUAC_MAIN='/root/quac/main.py'

# extract_type_annotations-related

EXTRACT_TYPE_ANNOTATIONS_MAIN='/root/extract_type_annotations/main.py'

# mypy-related

RUN_MYPY_PREFIX="conda run --no-capture-output --name mypy"
USE_MYPY_TO_CHECK_EACH_TYPE_PREDICTION='/root/use_mypy_to_check_each_type_prediction.py'
