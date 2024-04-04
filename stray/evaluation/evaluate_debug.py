from email.policy import default
from random import choice, choices
import os
import ast
from klara.core.cfg import Cfg
from klara.core.tree_rewriter import AstBuilder
from textwrap import dedent
from collections import defaultdict, deque
import re
from run_unittest_on_metric import fis, packages, ds, pk, remove_any, remove_nan, remove_none, same_ds, same_ds_, same_pk, same_pk_, same_type_recall, same_type, pure, real_name, read_ret

builtins = ['int', 'float','bool','str', 'byte', 'callable', 'none', 'object']
third = ['ndarray', 'tensor', 'namespace', 'vocabulary', 'textfieldembedder', 'jsondict', 'instance', 'socket', 'token']

projects = ['seagull','tinychain','relex','htmlark', 'pendulum', 'adventure', 'imp', 'icemu', 'scion', 'test_suite'][:5]
# returnses = [
# [0, 2, 4, 6, 9, 11, 13, 15, 18, 19, 21, 25, 27, 29, 30, 32, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 61, 63, 65],
# [0,1,2,3,5,7,8,10,13,16,19,22,23,25,26,27,33,36,39,41,44,45,47,48,53,57,62,64,66,68,70,73,76,79,82,85,88,90,93,95,97,98,100,102,104,],
# [0, 2, 9, 11, 13, 16, 23, 25, 28, 31, 33, 34],
# [0, 1, 3, 6, 14, 15],
# [0,3,6,7,8,9,10,11,13,15,17,20,21,24,26,27,30,31,34,35,36,37,40,41,42,43,44,45,46,48,51,53,55,57,59,60,61,62,63,64,65,66,67,69,71,72,74,75,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,101,102,103,105,107,108,109,111,113,115,117,122,123,126,129,134,139,141,143,145,147,149,152,156,162,163,165,166,168,169,170,171,172,173,174,175,176,177,178,179,180,181,184,187,188,189,191,193,195,196,198,200,202,204,206,207,208,209,211,213,214,216,217,219,224,226,228,229,230,232,234,235,237,239,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,269,274,276,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,295,296,297,301,305,306,307,308,310,312,321,330,332,334,337,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,362,365,367,369,372,374,376,379,381,383,386,388,390,392,394,396,398,399,401,402,404,407,411,412,413,414,415,416,417,418,419,420,421,424,427,428,429,430,431,433,435,440,445,447,449,451,453,456,460,461,462,463,464,465,466,467,468,469,470,471,472,474,476,478,480,483,485,487,490,492,494,497,499,503,504,507,515,518,520,523,525,527,529,531,532,533,534,537,539,541,543,545,547,548,549,550,551,552,554,556,557,558,559,564,566,568,571,573,575,578,581,584,587,591,593,596,599,602,604,605,608,609,611,612,614,618,620,623,626,629,632,634,637,], 
# [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 16, 18, 19, 21, 22, 23, 24, 26, 28, 30, 34, 36, 40, 44, 48, 53, 57, 61, 65, 70, 74, 78, 82, 89],
# [0, 3, 5, 6, 8, 10, 12, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41, 44, 46, 48, 49, 51, 52, 54, 55, 57, 58, 60, 61, 63, 64, 66, 67, 69, 70, 72, 73, 75, 76, 78, 79, 81],
# [0,1,2,3,5,6,7,8,9,10,11,13,17,18,19,20,22,24,27,29,30,34,35,38,40,41,42,43,44,45,47,48,50,51,53,54,56,58,60,62,],
# [0, 2, 4, 6, 8, 11, 12, 13, 14, 16, 18, 20, 21, 22, 23, 24, 25, 26, 29, 32, 33, 35, 36, 38, 39, 40, 42, 44, 48, 50, 52, 54, 56, 58, 59, 61, 62, 64, 66, 67, 69, 70, 71, 72, 73, 74, 77, 79, 80, 82, 84],
# [0,1,2,3,4,5,7,9,11,13,14,15,17,19,21,23,25,27,29,31,33,35,37,39,42,43,45,47,49,51,52,53,55,57,59,61,63,65,66,67,68,69,71,72,74,75,77,80,82,84,86,88,90,91,92,93,94,96,98,100,101,102,104,108,109,115,117,119,123,124,127,129,131,132,134,135,137,138,140,141,143,144,146,147,149,150,152,153,155,156,158,159,161,162,164,166,169,172,173,175,177,180,181,182,184,185,187,189,191,194,198,200,202,204,207,209,212,213,214,216,218,219,221,223,225,228,231,233,237,238,239,240,241,242,243,244,245,249,250,251,252,253,254,255,256,257,259,261,263,265,266,267,269,270,271,272,273,276,279,281,284,286,289,],

# ][9:10]

# special types like any, none and callable are sensitive
check_ret = True
ignore_no_res = False
ignore_ground_no_return = False

all_precisions = 0
all_recalls = 0
all_f1s = 0
all_cnt = 0
mrrs = 0
no_match_ground = []
# models = ['pytype', 'typilus', 'TW', 'PIG']
models = ['pytype', 'typilus', 'TW', 'pyre', 'PIG']
# models = ['TW', 'PIG']
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
            with open(f'{model}-t-{k}', 'w+') as f:
                pass
            with open(f'{model}-f-{k}', 'w+') as f:
                pass
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
                f = f'/home/sunke/dl-type-python/results/{model}_{project}.txt'
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
                        if hit_accuracy > 0:
                            pass

                            # print(i)
                        hit_recall = sum([same_type_recall(x, p) or same_ds(x, p) or same_pk(x,p) for x in g])
                        mrr = calc_mrr(p, g)
                        # with open('xxx', 'a+') as f:

                        #     f.write(str(i) + ' ' + str(hit_accuracy)+'\n')
                        # if not hit_accuracy and p[0]!='any':
                        #     # print(i)
                        #     no_match_ground.append((project, i, p ,g))
                        #     c +=1
                        with open('hit1', 'a+') as f:
                            f.write(str(i) + ':' + str(hit_accuracy)+'\n')
                        # print(hit_accuracy)
                        if k == 1 and hit_recall > 0 :
                            with open(f'{model}-t-{k}', 'a+') as f:
                                f.write(str(i) + ':' + str(p)+'\t'+str(g)+'\n')
                        if k == 1 and hit_recall == 0:
                            with open(f'{model}-f-{k}', 'a+') as f:
                                f.write(str(i) + ':' + str(p)+'\t'+str(g)+'\n')
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
            


with open('table.txt', 'w+') as f:

    f.write('$P_1$ & ' + ' & '.join(P[1]) + '\\\\ \\hline' +'\n')
    f.write('$R_1$ & ' + ' & '.join(R[1]) + '\\\\ \\hline' +'\n')
    f.write('$F1_1$ & ' + ' & '.join(F1[1])+ '\\\\ \\hline' +'\n')
    f.write('$P_3$ & ' + ' & '.join(P[3]) + '\\\\ \\hline' +'\n')
    f.write('$R_3$ & ' + ' & '.join(R[3]) + '\\\\ \\hline' +'\n')
    f.write('$F1_3$ & ' + ' & '.join(F1[3])+ '\\\\ \\hline' +'\n')
    f.write('$MRR$ & ' + ' & '.join(MRR[3])+ '\\\\ \\hline' +'\n')
    

    # print(R[1])
    # print(F1[1])

    # print(P[3])
    # print(R[3])
    # print(F1[3])

# with open('evaluation/examined_arg', 'w+') as f:
#     # c = choices(no_match_ground, k = 100)
#     for n in no_match_ground:
#         f.write(str(n)+'\n')
# # print('all')
# print('----------------------')
# print(all_precisions/all_cnt)
# print(all_recalls/all_cnt)
# print(all_f1s/all_cnt)
# print(all_cnt)
