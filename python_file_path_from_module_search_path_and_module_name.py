import os
import os.path


# module_search_path: 'github-repos/MonkeyType'
# module_name: 'demo.test_inbox'
# return: 'github-repos/MonkeyType/demo/test_inbox.py'
def python_file_path_from_module_search_path_and_module_name(
    module_search_path: str,
    module_name: str
) -> str:
    module_name_components = module_name.split('.')
    python_file_relpath_without_ext: str = os.path.sep.join(module_name_components)

    potential_directory_path: str = os.path.join(module_search_path, python_file_relpath_without_ext)

    # Module points to a directory
    if os.path.isdir(potential_directory_path):
        return os.path.join(potential_directory_path, '__init__.py')
    # Module points to a file
    else:
        return potential_directory_path + '.py'
