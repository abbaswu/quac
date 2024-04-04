import os
import os.path
import shutil


def copy_directory(
    source_dir: str,
    target_dir: str
):
    # This code snippet will create the directory specified in the path along with any necessary parent directories.
    # If the directory already exists, exist_ok=True prevents the function from raising an error, making it behave similarly to mkdir -p.
    os.makedirs(target_dir, exist_ok=True)

    # Copy each file and sub-directory from source_dir to type_prediction_temp_dir
    for item in os.listdir(source_dir):
        source_item = os.path.join(source_dir, item)
        destination_item = os.path.join(target_dir, item)

        if os.path.isdir(source_item):
            # If it's a directory, copy it recursively
            shutil.copytree(source_item, destination_item, dirs_exist_ok=True)
        else:
            # If it's a file, copy it
            shutil.copy2(source_item, destination_item)
