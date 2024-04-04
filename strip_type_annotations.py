import argparse
import ast
import logging
import os
import os.path
import sys


class TypeAnnotationStripper(ast.NodeTransformer):
    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef):
        # Remove return type annotation
        node.returns = None
        return self.generic_visit(node)

    def visit_FunctionDef(self, node: ast.FunctionDef):
        # Remove return type annotation
        node.returns = None
        return self.generic_visit(node)

    def visit_arg(self, node: ast.arg):
        # Remove argument type annotation
        node.annotation = None
        return self.generic_visit(node)


def is_valid_python_code(code: str) -> bool:
    try:
        module: ast.Module = ast.parse(code)
        return True
    except:
        return False


def strip_type_annotations(directory: str) -> None:
    type_annotation_stripper = TypeAnnotationStripper()
    for path, directory_names, file_names in os.walk(directory):
        for file_name in file_names:
            if file_name.endswith('.py'):
                file_path = os.path.join(path, file_name)
                try:
                    fp = open(file_path, 'r')
                    code: str = fp.read()
                    fp.close()

                    module: ast.Module = ast.parse(code)
                    transformed_module = type_annotation_stripper.visit(module)
                    transformed_code = ast.unparse(transformed_module)
                    assert is_valid_python_code(transformed_code)

                    fp = open(file_path, 'w')
                    fp.write(transformed_code)
                    fp.write('\n')
                    fp.close()

                    logging.info('Successfully stripped type annotations in file %s', file_path)
                except Exception:
                    logging.exception('Failed to handle file %s', file_path)


if __name__ == '__main__':
    # set up logging
    FORMAT = '%(asctime)s %(message)s'
    logging.basicConfig(format=FORMAT, level=logging.INFO)

    parser = argparse.ArgumentParser()
    parser.add_argument('-d', '--directory', type=str, required=True, help='directory')
    args = parser.parse_args()

    directory: str = args.directory

    strip_type_annotations(directory)

