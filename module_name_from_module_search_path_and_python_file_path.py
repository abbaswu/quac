import os
import os.path


# module_search_path: 'github-repos/MonkeyType'
# python_file_path: 'github-repos/MonkeyType/demo/test_inbox.py'
# return: 'demo.test_inbox'
def module_name_from_module_search_path_and_python_file_path(
    module_search_path: str,
    python_file_path: str
) -> str:
    python_file_relpath: str = os.path.relpath(python_file_path, module_search_path)
    python_file_relpath_without_ext, _ = os.path.splitext(python_file_relpath)
    python_file_relpath_without_ext_components = python_file_relpath_without_ext.split(os.path.sep)
    
    if python_file_relpath_without_ext_components[-1] == '__init__':
        return '.'.join(python_file_relpath_without_ext_components[:-1])
    else:
        return '.'.join(python_file_relpath_without_ext_components)

