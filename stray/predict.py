from extyper.main import process_options
import sys
from extyper import build
from extyper.fscache import FileSystemCache
import os
from extyper.remover import TypeHintRemover
import ast
args = sys.argv[1:]
mode = args[1]
tag = args[2]
args = args[0:1]
print(args)


def build_cache(options):
    options.check_untyped_defs = True
    options.allow_redefinition = True
    options.incremental = True
    options.use_builtins_fixtures = False 
    options.show_traceback = False
    options.error_summary = False
    options.fine_grained_incremental = False
    options.use_fine_grained_cache = False
    options.cache_fine_grained = False
    options.local_partial_types = False
    options.preserve_asts = True
    options.export_types = True
    options.check_untyped_defs = True
    options.strict_optional = True
    options.show_column_numbers = True
    
    return options
def order_function(order):
    return []

fscache = FileSystemCache()

def clear_annotation(path):
    source = open(path).read()
    # parse the source code into an AST
    parsed_source = ast.parse(source)
    # remove all type annotations, function return type definitions
    # and import statements from 'typing'
    transformed = TypeHintRemover().visit(parsed_source)
    # convert the AST back to source code
    transformed_code = ast.unparse(transformed)

    with open(path, 'w+') as f:
        f.write(transformed_code)
def clear_cache(module):
    module = module.replace('.','/')
    path1 = '.mypy_cache/3.9/' + module + '.data.json'
    path2 = '.mypy_cache/3.9/' + module + '.meta.json'
    if os.path.exists(path1):
        os.remove(path1)
    if os.path.exists(path2):
        os.remove(path2)
    path1 = '.mypy_cache/3.9/' + module + '/__init__.data.json'
    path2 = '.mypy_cache/3.9/' + module + '/__init__.meta.json'
    if os.path.exists(path1):
        os.remove(path1)
    if os.path.exists(path2):
        os.remove(path2)
    
sources, options = process_options(args, stdout=sys.stdout, stderr=sys.stderr,
                                    fscache=fscache)
options.tag = tag
options.mode = mode
for source in sources:
    # clear_annotation(source.path)
    clear_cache(source.module)
modules = [x.module for x in sources]
options = build_cache(options)

result = build.build(sources=sources, options=options, modules=modules)