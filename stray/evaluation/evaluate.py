from email.policy import default
from random import choice, choices
import os
import ast
import sys
from textwrap import dedent
from collections import defaultdict, deque
import re
from run_unittest_on_metric import fis, packages, ds, pk, remove_any, remove_nan, remove_none, same_ds, same_ds_, same_pk, same_pk_, same_type_recall, same_type, pure, real_name, read_ret

builtins = ['int', 'float','bool','str', 'byte', 'callable', 'none', 'object']
third = ['ndarray', 'tensor', 'namespace', 'vocabulary', 'textfieldembedder', 'jsondict', 'instance', 'socket', 'token']

projects = ['seagull','tinychain','relex','htmlark', 'pendulum', 'adventure', 'imp', 'icemu', 'scion', 'test_suite']

# special types like any, none and callable are sensitive

args = sys.argv[1:]
MODE = args[0]
if MODE == 'return':

    check_ret = True
else:
    check_ret = False


ignore_no_res = False
ignore_ground_no_return = False

all_precisions = 0
all_recalls = 0
all_f1s = 0
all_cnt = 0
mrrs = 0
no_match_ground = []

models = ['pytype', 'typilus', 'TW', 'pyre', 'PIG']

P = defaultdict(list)
R = defaultdict(list)
F1 = defaultdict(list)
MRR = defaultdict(list)
cc = 0
for k in [1,3]:
    for ii, project in enumerate(projects):
        if project == 'pendulum' :
            lower = False
        else:
            lower = True
        for model in models:
        # if i == 4:
        #     lower = False
            print(model + '---' + project + '---' + str(k))
            print('----------------------')
            ground_truth = []
            returns = read_ret(project)
            with open(f'evaluation/GT_{project}.txt') as f:
                
                for i, line in enumerate(f):
                    if lower:
                        line = line.lower()
                    ground_truth.append(line.strip().split('/'))
            PIG = []
            if model == 'TW':
                f = f'evaluation/{model}_{project}.txt'
            elif model == 'PIG':
                f = f'results/funcs_res-{project}'
            else:
                f = f'evaluation/{model}_{project}.txt'
            with open(f) as f:
                
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
                    if same_type(x, g) or same_ds(x, g) or same_pk(x,g):
                        return 1/(i + 1)
                return 0
            c = 0
            for i, p in enumerate(PIG):
                # p = remove_none(p)
                p = remove_nan(p)
                if model == 'pytype' and len(p) == 1 and p[0]== '':
                    # we do not copy any but set here
                    p = ['any']

                
                p = p[:k]
                if check_ret:
                    b = i in returns
                else:
                    b = i not in returns
                if b:
                    cc += 1
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
                    if not ignore_no_res and (len(p) == 0 or p[0] == ''):
                        p = ['<xxx>']
                    if len(p) > 0 and p[0] != '':
                        
                        cnt += 1
                        hit_accuracy = sum([same_type(x, g) or same_ds(x, g) or same_pk(x,g) for x in p])
                        hit_recall = sum([same_type_recall(x, p) or same_ds(x, p) or same_pk(x,p) for x in g])
                        mrr = calc_mrr(p, g)
                        precision = hit_accuracy/len(p)
                        recall = hit_recall/len(g)
                        
                        if precision + recall == 0:
                            f1 = 0
                        else:
                            f1 = (2*precision*recall)/(precision + recall)
                        precisions += precision
                        recalls += recall
                        mrrs += mrr
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
                    MRR[k].append('\\textbackslash{}')
                    
                elif model == 'PIG':
                    P[k].append('\\textbf{' + '{:.2f}'.format(round(precisions/cnt, 2)) + '}')
                    R[k].append('\\textbf{' + '{:.2f}'.format(round(recalls/cnt, 2)) + '}')
                    F1[k].append('\\textbf{' + '{:.2f}'.format(round(f1s/cnt, 2)) + '}')
                    MRR[k].append('\\textbf{' + '{:.2f}'.format(round(mrrs/cnt, 2)) + '}')
                    
                else:
                    P[k].append('{:.2f}'.format(round(precisions/cnt, 2)))
                    R[k].append('{:.2f}'.format(round(recalls/cnt, 2)))
                    F1[k].append('{:.2f}'.format(round(f1s/cnt, 2)))
                    MRR[k].append('{:.2f}'.format(round(mrrs/cnt, 2)))
                    
                    
            all_precisions += precisions
            all_recalls += recalls
            all_f1s += f1s
            all_cnt += cnt
            

if check_ret:
    fn = 'table_return.txt'
else:
    fn = 'table_parameter.txt'
with open(fn, 'w+') as f:

    f.write('$P_1$ & ' + ' & '.join(P[1]) + '\\\\ \\hline' +'\n')
    f.write('$R_1$ & ' + ' & '.join(R[1]) + '\\\\ \\hline' +'\n')
    f.write('$F1_1$ & ' + ' & '.join(F1[1])+ '\\\\ \\hline' +'\n')
    f.write('$MRR_1$ & ' + ' & '.join(MRR[1])+ '\\\\ \\hline' +'\n')
    
    f.write('$P_3$ & ' + ' & '.join(P[3]) + '\\\\ \\hline' +'\n')
    f.write('$R_3$ & ' + ' & '.join(R[3]) + '\\\\ \\hline' +'\n')
    f.write('$F1_3$ & ' + ' & '.join(F1[3])+ '\\\\ \\hline' +'\n')
    f.write('$MRR_3$ & ' + ' & '.join(MRR[3])+ '\\\\ \\hline' +'\n')
    


