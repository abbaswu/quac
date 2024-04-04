EXPERIMENT_ROOT="$(dirname "$0")"
source $EXPERIMENT_ROOT/parameters.sh

# Variables from command-line arguments

# Query dict, pass with option `-q`
query_dict=

# Module search path, pass with option `-s`
module_search_path=

# Output file path, pass with option `-o`
output_file_path=

# Raw output directory, pass with option `-r`
raw_output_directory=

while getopts ':q:s:o:r:' name
do
    case $name in
        q)
            query_dict="$OPTARG"
            ;;
        s)
            # Module search path MUST NOT end with '/'s, otherwise breaks hityper
            module_search_path="$(echo "$OPTARG" | sed 's/\/\+$//')"
            ;;
        o)
            output_file_path="$OPTARG"
            ;;
        r)
            raw_output_directory="$OPTARG"
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

if [ -z "$query_dict" ] || [ -z "$module_search_path" ] || [ -z "$output_file_path" ] || [ -z "$raw_output_directory" ]
then
    echo "Usage: $0 -q <query_dict> -s <module_search_path> -o <output_file_path> -r <raw_output_directory>" >&2
    exit 1
fi

if ! [ -d "$module_search_path" ]
then
    echo "Module search path ${module_search_path} is not a directory!" >&2
    exit 1
fi

mkdir -p "$STRAY_ROOT/result"
mkdir -p "$STRAY_ROOT/results"

absolute_module_search_path="$(realpath "$module_search_path")"

current_working_directory="$(pwd)"

cd "$STRAY_ROOT"

set +e

python3 "$PRINT_PYTHON_FILE_PATHS" -q "$query_dict" -s "$absolute_module_search_path" | while read -r python_file_path
do
    directory_name="$(dirname "$python_file_path")"
    file_name="$(basename "$python_file_path")"
    file_name_without_extension="${file_name%.py}"

    echo conda run --no-capture-output --name stray python3 -m predict "$directory_name" check "$file_name_without_extension" 1>&2
    conda run --no-capture-output --name stray python3 -m predict "$directory_name" check "$file_name_without_extension" 1>&2
    echo conda run --no-capture-output --name stray python3 -m predict "$directory_name" check "$file_name_without_extension" 1>&2
    conda run --no-capture-output --name stray python3 -m predict "$directory_name" predict "$file_name_without_extension" 1>&2
done

set -e
set -o pipefail

cd "$current_working_directory"

python3 "$PARSE_STRAY_RESULT_DIRECTORY" --stray-result-directory "$STRAY_ROOT/result" --query-dict "$query_dict" --absolute-module-search-path "$absolute_module_search_path" --output-file "$output_file_path"

cp -R -v "$STRAY_ROOT/result" "$raw_output_directory"
