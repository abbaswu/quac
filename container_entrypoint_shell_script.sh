#!/bin/bash

set -e
set -o pipefail


EXPERIMENT_ROOT="$(dirname "$0")"
source "${EXPERIMENT_ROOT}/parameters.sh"

# Variables from command-line arguments

# Method, pass with option `-m`
method=

# Module prefix, pass with `-p`
module_prefix=

while getopts ':m:p:' name
do
    case $name in
        m)
            method="$OPTARG"
            ;;
        p)
            module_prefix="$OPTARG"
            ;;
        :)
            echo "Option -$OPTARG requires an argument"
            ;;
        ?)
            echo "Invalid option -$OPTARG"
            ;;
    esac
done

# Sanity check

if [ ! -d "$MOUNTED_MODULE_SEARCH_PATH" ]
then
    echo "Module search path is not mounted to ${MOUNTED_MODULE_SEARCH_PATH}" >&2
    echo "Please provide a mount point with your Docker run command: " >&2
    echo "docker run --net=host -v <module_search_path>:${MOUNTED_MODULE_SEARCH_PATH}:ro -v <output_path>:${OUTPUT_PATH} ..." >&2
    exit 1
fi

if [ ! -d "$OUTPUT_PATH" ]
then
    echo "Output path is not mounted to ${OUTPUT_PATH}" >&2
    echo "Please provide a mount point with your Docker run command: " >&2
    echo "docker run --net=host -v <module_search_path>:${MOUNTED_MODULE_SEARCH_PATH}:ro -v <output_path>:${OUTPUT_PATH} ..." >&2
    exit 1
fi

if [ -z "$method" ] || [ -z "$module_prefix" ]
then
    echo "Usage: $0 -m <method> -p <module_prefix>" >&2
    exit 1
fi

if ! python3 "$IS_PORT_IN_USE" -p 5001
then
    echo "Type4Py server not available on port 5001!" >&2
    echo "Make sure that you have started Type4Py server outside of this container:" >&2
    echo '''
    docker pull ghcr.io/saltudelft/type4py:latest
    docker run -d -p 5001:5010 -it ghcr.io/saltudelft/type4py:latest
    ''' >&2
    echo "docker run --net=host -v <module_search_path>:${MOUNTED_MODULE_SEARCH_PATH}:ro -v <output_path>:${OUTPUT_PATH} ..." >&2
    exit 1
fi

# Preprocessing

# Copy contents from $MOUNTED_MODULE_SEARCH_PATH to $LOCAL_MODULE_SEARCH_PATH
cp -R "$MOUNTED_MODULE_SEARCH_PATH" "$LOCAL_MODULE_SEARCH_PATH"

# Generate query dict for repository
python3 "$GENERATE_QUERY_DICT_FOR_REPOSITORY" \
	--module-search-path "$LOCAL_MODULE_SEARCH_PATH" \
	--module-prefix "$module_prefix" \
	--output-query-dict "$QUERY_DICT_JSON"

# Run method, modifying the contents of $LOCAL_MODULE_SEARCH_PATH
case "$method" in
    # pyre)
    #     pyre_output_file="$LOCAL_MODULE_SEARCH_PATH/pyre_output_file"

    #     conda run --no-capture-output --name pyre pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
    #     # Prompt:
    #     # Also initialize watchman in the current directory? [Y/n]
    #     # Which directory(ies) should pyre analyze? (Default: `.`):
    #     printf "Y\n${LOCAL_MODULE_SEARCH_PATH}\n" | conda run --no-capture-output --name pyre pyre init
    #     conda run --no-capture-output --name pyre pyre infer --print-only > "$pyre_output_file" 2>&1

    #     cat "$pyre_output_file" | python3 "$(pwd)/parse_pyre_stdout.py" --query-dict "$query_dict" > "$output_file_path"
    #     ;;
    # pytype)
    #     conda run --no-capture-output --name pytype pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
    #     conda run --no-capture-output --name pytype pytype --keep-going "$LOCAL_MODULE_SEARCH_PATH" 1>&2

    #     pytype_pyi_directory="$(pwd)/.pytype/pyi"

    #     # Import-based analysis, MUST use pytype's virtual environment that has all the requirements installed
    #     conda run --no-capture-output --name pytype python3 "$(pwd)/parse_pytype_result_directory.py" --query-dict "$query_dict" --module-search-path "$LOCAL_MODULE_SEARCH_PATH" --pytype-pyi-directory "$pytype_pyi_directory" > "$output_file_path"
    #     ;;
    quac)
        # Strip type annotations from Python files
        python3 "$STRIP_TYPE_ANNOTATIONS" --directory "$LOCAL_MODULE_SEARCH_PATH"

        if [ -f "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" ]; then
            conda run --no-capture-output --name quac pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
        fi

        mkdir -p "$RAW_OUTPUT_DIRECTORY"
        class_inference_log_file="$RAW_OUTPUT_DIRECTORY/class_inference_log_file.jsonl"

        PYTHONPATH="$LOCAL_MODULE_SEARCH_PATH" \
        /usr/bin/time \
        -f '{"maximum resident set size in KB": %M, "elapsed real time (wall clock) in seconds": %e}' \
        -o "$TIME_OUTPUT_JSON" \
        conda run --no-capture-output --name quac \
        python3 "$QUAC_MAIN" \
	--module-search-path "$LOCAL_MODULE_SEARCH_PATH" \
	--module-prefix "$module_prefix" \
	--output-file "$OUTPUT_JSON" \
        --query-dict "$QUERY_DICT_JSON"
        ;;
    stray)
        # Strip type annotations from Python files
        python3 "$STRIP_TYPE_ANNOTATIONS" --directory "$LOCAL_MODULE_SEARCH_PATH"

        if [ -f "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" ]; then
            conda run --no-capture-output --name stray pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
        fi

        /usr/bin/time \
        -f '{"maximum resident set size in KB": %M, "elapsed real time (wall clock) in seconds": %e}' \
        -o "$TIME_OUTPUT_JSON" \
        bash "$RUN_STRAY" \
        -q "$QUERY_DICT_JSON" \
        -s "$LOCAL_MODULE_SEARCH_PATH" \
        -o "$OUTPUT_JSON" \
        -r "$RAW_OUTPUT_DIRECTORY"
        ;;
    hityper)
        # Strip type annotations from Python files
        python3 "$STRIP_TYPE_ANNOTATIONS" --directory "$LOCAL_MODULE_SEARCH_PATH"

        if [ -f "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" ]; then
            conda run --no-capture-output --name hityper pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
        fi

        /usr/bin/time \
        -f '{"maximum resident set size in KB": %M, "elapsed real time (wall clock) in seconds": %e}' \
        -o "$TIME_OUTPUT_JSON" \
        bash "$RUN_HITYPER" \
        -q "$QUERY_DICT_JSON" \
        -s "$LOCAL_MODULE_SEARCH_PATH" \
        -o "$OUTPUT_JSON" \
        -r "$RAW_OUTPUT_DIRECTORY"
        ;;
    extract_type_annotations)
        if [ -f "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" ]; then
            conda run --no-capture-output --name extract_type_annotations pip install -r "${LOCAL_MODULE_SEARCH_PATH}/requirements.txt" 1>&2
        fi

        PYTHONPATH="$LOCAL_MODULE_SEARCH_PATH" \
        /usr/bin/time \
        -f '{"maximum resident set size in KB": %M, "elapsed real time (wall clock) in seconds": %e}' \
        -o "$TIME_OUTPUT_JSON" \
        conda run --no-capture-output --name extract_type_annotations \
        python3 "$EXTRACT_TYPE_ANNOTATIONS_MAIN" \
        --module-search-path "$LOCAL_MODULE_SEARCH_PATH" \
        --module-prefix "$module_prefix" \
        --output-file "$OUTPUT_JSON"

        # Strip type annotations from Python files
        python3 "$STRIP_TYPE_ANNOTATIONS" --directory "$LOCAL_MODULE_SEARCH_PATH"
        ;;
    *)
        # error
        echo "Invalid method `$method`." >&2
        exit 1
esac

# Use mypy to check each type prediction
python3 "$USE_MYPY_TO_CHECK_EACH_TYPE_PREDICTION" \
	--module-search-path "$MOUNTED_MODULE_SEARCH_PATH" \
	--module-prefix "$module_prefix" \
	--type-predictions-json-path "$OUTPUT_JSON" \
	--output-directory-path "$TYPE_CHECKING_OUTPUT_DIRECTORY" \
	--output-csv-path "$TYPE_CHECKING_OUTPUT_CSV" \
	--run-mypy-prefix "$RUN_MYPY_PREFIX"
