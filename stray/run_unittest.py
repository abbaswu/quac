from extyper.main import process_options
import sys
from extyper import build
from extyper.fscache import FileSystemCache
import os
from extyper.remover import TypeHintRemover
import ast
from tqdm import tqdm

test_folder = "data/benchmark/unittests"
gen = False
start = 0
skiped = ['relex.py', 'imp.py', 'reserved.py', 'test_big.py'] # ['tinychain.py', 'default_none.py', 'inline_test.py']
take = ['tinychain.py']

def generate(file):
    mode = 'predict'
    args = [file]
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
    options.mode = mode
    for source in sources:
        # clear_annotation(source.path)
        clear_cache(source.module)
    modules = [x.module for x in sources]
    options = build_cache(options)

    result = build.build(sources=sources, options=options, modules=modules)


def diff(file):
    mode = 'predict'
    args = [file]
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
    options.mode = mode
    for source in sources:
        # clear_annotation(source.path)
        clear_cache(source.module)
    modules = [x.module for x in sources]
    options = build_cache(options)
    result_fi = result_file(file)
    oracle = open(result_fi).read()

    with open(result_fi + '_temp', 'w+') as f:
        f.write(oracle)
    try:
        result = build.build(sources=sources, options=options, modules=modules)
    except Exception:
        # in case of crashes
        with open(result_fi, 'w+') as f:
            f.write(oracle)
        assert False
    res = open(result_fi).read()
    if oracle != res:
        with open(result_fi, 'w+') as f:
            f.write(oracle)
        with open(result_fi + '_temp', 'w+') as f:
            f.write(res)
    assert oracle == res
def result_file(fi):
    return 'result/' + fi.replace('/', '-') +'_whole_'

i = 0
for f in tqdm(os.listdir(test_folder)):
    i += 1
    if i-1 <= start:
        continue
    if take and f not in take:
        continue
    if not f.endswith('.py') or f in skiped:
        continue
    print(f)
    fi = os.path.join(test_folder, f)
    if gen:
        generate(fi)
    else:
        diff(fi)
    