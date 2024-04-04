from email.policy import default
from random import choice, choices

import ast
from klara.core.cfg import Cfg
from klara.core.tree_rewriter import AstBuilder
from textwrap import dedent
from collections import defaultdict, deque
import re
from extyper.main import process_options
import sys
from extyper import build
from extyper.fscache import FileSystemCache
import os
from extyper.remover import TypeHintRemover
import ast
from tqdm import tqdm
import json

TEST = True
args = sys.argv[1:]
MODE = args[0]

builtins = ['int', 'float','bool','str', 'byte', 'callable', 'none', 'object']
third = ['ndarray', 'tensor', 'namespace', 'vocabulary', 'textfieldembedder', 'jsondict', 'instance', 'socket', 'token']

fis = {
    'seagull': 'data/benchmark/seagull',
    'tinychain': 'data/benchmark/tinychain',
    'relex': 'data/benchmark/relex',
    'htmlark': 'data/benchmark/htmlark',
    'adventure': 'data/benchmark/adventure',
    'imp': 'data/benchmark/imp',
    'icemu': 'data/benchmark/icemu',
    'scion': 'data/benchmark/scion',
    'test_suite': 'data/benchmark/test_suite',
    'pendulum': 'data/benchmark/pendulum'
}
projects = ['seagull','tinychain','relex','htmlark', 'pendulum', 'adventure', 'imp', 'icemu', 'scion', 'test_suite']
fast_test_projects = ['seagull', 'tinychain', 'adventure', 'imp', 'icemu', 'scion', 'test_suite']
# fast_test_projects = ['relex']

if TEST:
    projects = fast_test_projects
# special types like any, none and callable are sensitive

lower = True
check_ret = False
mass_object = True
mass_container = True
mass_bool = True
ignore_no_res = False
ignore_ground_no_return = False
numberic_tower = True

all_precisions = 0
all_recalls = 0
all_f1s = 0
all_cnt = 0
mrrs = 0
no_match_ground = []
packages = ['test_suite', 'unittests_typpete', 'pcb', 'benchmark', 'typing', 'numpy', 'builtins', 'np', 'tinychain', 'allennlp', 'data', 'instance', 'torch', '_tensor', 'argparse', 'seagull_new', 'seagull', 'adventure', 'chip', 'lib', 'packet', 'scion_addr', 'imp', 'scion', ]
for p in os.listdir(fis['test_suite']):
    packages.append(p.replace('.py',''))
packages = set(packages)
for p in os.walk(fis['pendulum']):
    folder, _, files = p
    packages.update(folder.split('/'))
    for f in files:
        if f.endswith('.py'):
            packages.add(f.replace('.py',''))

ds = ['list','set','tuple','dict']
pk = ['ndarray', 'IO', 'io']
def pure(typ):
    typ = typ.replace('*','').replace('?','')
    if typ.startswith('optional[') and typ.endswith(']'):
        typ = typ[9:-1]
    if typ.startswith('Optional[') and typ.endswith(']'):
        typ = typ[9:-1]
    
    return typ

def real_name(typ):
    for p in sorted(packages, key=lambda k:len(k), reverse=True):
        typ = typ.replace(f'{p}.','')
    return typ
models = ['pytype', 'typilus', 'TW', 'PIG']
# models = ['TW']
P = defaultdict(list)
R = defaultdict(list)
F1 = defaultdict(list)
MRR = defaultdict(list)

def run(file, tag):
    mode = MODE
    
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
    options.tag = tag
    for source in sources:
        # clear_annotation(source.path)
        clear_cache(source.module)
    modules = [x.module for x in sources]
    options = build_cache(options)
    result = build.build(sources=sources, options=options, modules=modules)

def read_ground_truth(project):
    ground_truth = []
    with open(f'evaluation/GT_{project}.txt') as f:
                
        for i, line in enumerate(f):
            if lower:
                line = line.lower()
            ground_truth.append(line.strip().split('/'))
    return ground_truth

def read_res(tag):
    PIG = []
    with open(f'results/funcs_res-{tag}') as f:
                
        for i, line in enumerate(f):
            if lower:
                line = line.lower()
            qualifier_names = line.strip().split('/')
            a = [pure(real_name(x)) for x in qualifier_names]
            b = []
            for aa in a:
                if aa not in b:
                    b.append(aa)
            PIG.append(b)
    return PIG
def read_ret(tag):
    ret = []
    with open(f'results/funcs_ret-{tag}') as f:
                
        ret = [int(x) for x in f.read().split(',')[:-1]]
    return ret


def remove_nan(p):
    return [x for x in p if x  != 'nan']
def remove_none(p):
    return [x for x in p if x  != 'none' and x != 'None']
def remove_any(p):

    return [x for x in p if x  != 'any' and x != 'Any']


def same_ds(x, g):
    for y in g:
        if same_ds_(x, y):
            return True

    return False
def same_pk(x, g):
    for y in g:
        if same_pk_(x, y):
            return True

    return False

def same_ds_(x, y):
    if not mass_container:
        return False
    global ds
    for d in ds:
        if x.find(d) != -1 and y.find(d) != -1:
            return True
    return False
def same_pk_(x, y):
    global pk
    for p in pk:
        if x.find(p) != -1 and y.find(p) != -1:
            return True
    return False
def same_type_recall(y, p):
    for x in p:
        if compatible(x,y) or coherent(x, y) or alias(x, y):
            return True
    return False

def compatible(x,y):
    # x:<y, since x should be valid if its a subtype of y  
    if x == y:
        return True
    if numberic_tower:
        if y == 'int':
            if x =='bool':
                return True
        if y == 'float':
            if x =='int':
                return True
            if x =='bool':
                return True
    
    if y == 'any' or y == 'Any':
        return True
    if mass_object and y == 'object':
        return True

    # seagull type hierarchy
    lifeforms = ['Custom','Glider','LightweightSpaceship','MiddleweightSpaceship','Unbounded','Century','Thunderbird','Blinker','Toad','Pulsar','FigureEight','Beacon','Pentadecathlon','ChaCha','RandomBox','Box','Seed','Moon','Kite','Eater1','SwitchEngine']
    lifeforms += [x.lower() for x in lifeforms]
    if x in lifeforms and y == 'lifeform':
        return True
    
    # tinychain type hierarchy
    namedtuples = ['TxIn', 'TxOut', 'UnspentTxOut', 'Transaction', 'Block', 'MerkleNode']
    namedtuples += [x.lower() for x in namedtuples]
    if x in namedtuples and y == 'namedtuple':
        return True
    

    # relex type hierarchy
    if x == 'RelationInstancesReader'.lower() and y == 'DatasetReader'.lower():
        return True
    if x == 'CombDistDirectRelex'.lower() and y == 'Model'.lower():
        return True
    if x == 'MultilabelAveragePrecision'.lower() and y == 'Metric'.lower():
        return True
    if x == 'RelationExtractionPredictor'.lower() and y == 'Predictor'.lower():
        return True
    
    # pendulum type hierarchy
    if y == 'Timezone' and x == 'FixedTimezone':
        return True

    if y == 'datetime' and x == 'DateTime':
        return True
    
    if y == 'time' and x == 'Time':
        return True
    if y == 'date' and x == 'Date':
        return True
    
    if y == 'timedelta' and x == 'Duration':
        return True
    if y == 'timedelta' and x == 'Duration':
        return True
    if y == 'tzinfo' and x == 'Timezone':
        return True
    
    # adventure type hierarchy
    hasns = ['Move', 'Room', 'Word', 'Object', 'Message', 'Hint']
    hasns += [x.lower() for x in hasns]
    if x in hasns and y == 'hasn':
        return True

    # imp type hierarchy

    parsers = ['Tag', 'Reserved', 'Concat', 'Exp', 'Alternate', 'Opt', 'Rep', 'Process', 'Lazy', 'Phrase']
    parsers += [x.lower() for x in parsers]
    if x in parsers and y == 'parser':
        return True

    equalities = ['Statement', 'Aexp', 'Bexp']
    equalities += [x.lower() for x in equalities]
    if x in equalities and y == 'equality':
        return True

    # icemu type hierarchy

    chips = ['ActivableChip', 'Segment7', 'Gate', 'Inverter']
    chips += [x.lower() for x in chips]
    if x in chips and y == 'chip':
        return True

    
def coherent(x,y):
    # x<:y, since x should be valid if its a subtype of y  
    if x == y:
        return True

    if mass_bool and y == 'bool':
        return True
    
    

def alias(x, y):
    fx = re.match( r'def (.*) ->', x, re.M|re.I)
    fy = re.match( r'def (.*) ->', y, re.M|re.I)
    
    if fx and y in ('callable', 'Callable'):
        return True
    if fy and x ('callable', 'Callable'):
        return True
    return False
def same_type(x, g):
    for y in g:
        if compatible(x,y) or coherent(x, y) or alias(x, y):
            return True

    return False
if __name__ == '__main__':
    for ii, project in enumerate(projects):

        
        fi = fis[project]
        run(fi, project)
        
        # no project label
        result_file = 'func_res'
        if project == 'pendulum':
            lower = False
        else:
            lower = True
        
        for k in [1,3]:
            for model in models:
            # if i == 4:
            #     lower = False
                print(model + '---' + project + '---' + str(k))
                print('----------------------')
                ground_truth = read_ground_truth(project)
                returns = read_ret(project)
                PIG = read_res(project)

            
                precisions = 0
                recalls = 0
                f1s = 0
                cnt = 0
                mrrs = 0
                

                def is_builtin(g):
                    for g_ in g:
                        if any(g_.find(x) != -1 for x in builtins):
                            return True
                    return False
                def is_third(g):
                    for g_ in g:
                        if any(g_.find(x) != -1 for x in third):
                            return True
                    return False

                def calc_mrr(p, g):
                    for i, x in enumerate(p):
                        if same_type(x, g):
                            return 1/(i + 1)
                    return 0
                c = 0
                for i, p in enumerate(PIG):
                    # p = remove_none(p)
                    p = remove_nan(p)
                    if model != 'pytype':
                        p = remove_any(p)

                    
                    p = p[:k]
                    if check_ret:
                        b = i in returns
                    else:
                        b = i not in returns
                    if b:
                        
                        g = ground_truth[i]
                        if 'any' in g or 'Any' in g:
                            continue
                        if len(g) == 1 and g[0]=='':
                            continue
                        
                        
                        if ignore_ground_no_return and ('none' in g or 'None' in g):
                            continue
                        # if is_builtin(g):
                        #     continue
                        # elif is_third(g):
                        #     continue
                        # else:
                        #     pass
                        if not ignore_no_res and len(p) == 0:
                            p = ['<xxx>']
                        if len(p) > 0 and p[0] != '':
                            
                            cnt += 1
                            hit_accuracy = sum([same_type(x, g) or same_ds(x, g) or same_pk(x,g) for x in p])
                            if hit_accuracy > 0:
                                pass

                                # print(i)
                            hit_recall = sum([same_type_recall(x, p) or same_ds(x, p) or same_pk(x,p) for x in g])

                            precision = hit_accuracy/len(p)
                            recall = hit_recall/len(g)
                            if precision + recall == 0:
                                f1 = 0
                            else:
                                f1 = (2*precision*recall)/(precision + recall)
                            precisions += precision
                            recalls += recall
                            # mrrs += mrr
                            f1s += f1
                            # print(precision)
                            # print(recall)
                            # print(f1)
                if cnt == 0:
                    print(0)
                    print(0)
                    print(0)
                    print(cnt)    
                else:
                    print(precisions)
                    print(recalls)
                    print(f1s)
                    
                    print(precisions/cnt)
                    print(recalls/cnt)
                    print(f1s/cnt)
                    # print(mrrs/cnt)
                    print(cnt)
                    if model in ['pytype', 'pyre'] and not check_ret:
                        P[k].append('\\textbackslash{}')
                        R[k].append('\\textbackslash{}')
                        F1[k].append('\\textbackslash{}')
                        # MRR[k].append('\\textbackslash{}')
                        
                    elif model == 'PIG':
                        P[k].append('\\textbf{' + str(round(precisions/cnt, 2)) + '}')
                        R[k].append('\\textbf{' + str(round(recalls/cnt, 2)) + '}')
                        F1[k].append('\\textbf{' + str(round(f1s/cnt, 2)) + '}')
                        # MRR[k].append('\\textbf{' + str(round(mrrs/cnt, 2)) + '}')
                        
                    else:
                        P[k].append(str(round(precisions/cnt, 2)))
                        R[k].append(str(round(recalls/cnt, 2)))
                        F1[k].append(str(round(f1s/cnt, 2)))
                        # MRR[k].append(str(round(mrrs/cnt, 2)))
                        
                all_precisions += precisions
                all_recalls += recalls
                all_f1s += f1s
                all_cnt += cnt
                


    with open('table2.txt', 'w+') as f:

        f.write('$P_1$ & ' + ' & '.join(P[1]) + '\\\\ \\hline' +'\n')
        f.write('$R_1$ & ' + ' & '.join(R[1]) + '\\\\ \\hline' +'\n')
        f.write('$F1_1$ & ' + ' & '.join(F1[1])+ '\\\\ \\hline' +'\n')
        # f.write('$MRR_1$ & ' + ' & '.join(MRR[1])+ '\\\\ \\hline' +'\n')
        
        f.write('$P_3$ & ' + ' & '.join(P[3]) + '\\\\ \\hline' +'\n')
        f.write('$R_3$ & ' + ' & '.join(R[3]) + '\\\\ \\hline' +'\n')
        f.write('$F1_3$ & ' + ' & '.join(F1[3])+ '\\\\ \\hline' +'\n')
        # f.write('$MRR_3$ & ' + ' & '.join(MRR[3])+ '\\\\ \\hline' +'\n')

