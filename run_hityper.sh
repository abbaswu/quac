set -e
set -o pipefail

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

hityper_output_directory="$(pwd)/hityper_output_directory"
mkdir -p "$hityper_output_directory"

python3 "$PRINT_PYTHON_FILE_PATHS" -q "$query_dict" -s "$module_search_path" | while read -r python_file_path
do
    echo conda run --no-capture-output --name hityper hityper infer -p "$module_search_path" -s "$python_file_path" -d "$hityper_output_directory" -t 1>&2
    conda run --no-capture-output --name hityper hityper infer -p "$module_search_path" -s "$python_file_path" -d "$hityper_output_directory" -t 1>&2
done

python3 "$PARSE_HITYPER_OUTPUT_DIRECTORY" --hityper-output-directory "$hityper_output_directory" --query-dict "$query_dict" --module-search-path "$module_search_path" --output-file "$output_file_path"

cp -R -v "$hityper_output_directory" "$raw_output_directory"
