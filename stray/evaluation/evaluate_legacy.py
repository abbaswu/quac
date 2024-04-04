from email.policy import default
from random import choice, choices

import ast
from klara.core.cfg import Cfg
from klara.core.tree_rewriter import AstBuilder
from textwrap import dedent
from collections import defaultdict, deque


prj = 'imp'
s = set()
with open(f'result/data-benchmark-unittests-{prj}.py_whole_') as f:
    for l in f:
        s.add(l.strip())


print(len(s))


builtins = ['int', 'float','bool','str', 'byte', 'callable', 'none', 'object']
third = ['ndarray', 'tensor', 'namespace', 'vocabulary', 'textfieldembedder', 'jsondict', 'instance', 'socket', 'token']


projects = ['seagull','tinychain','relex','htmlark', 'pendulum', 'adventure', 'imp', 'chip', 'scion', 'unittests'][5:]
returnses = [
[3,5,8,10,12,14,16,18,20,22,24,26,31,35,37,39,40,41,43,47,48,49,50,51,52,53,55,56,57,58,59,60,61,64,65,66,67,68,69],
[3,6,9,10,12,15,18,19,21,22,28,31,34,36,39,40,42,47,51,53,55,57,59,62,64,66,68,70,72,77,80,81,83,85,88,91,94,97,100,103],
[10, 17, 20, 23, 26, 28, 33, 36, 38, 40, 47, 49, 51],
[2, 4, 7, 15, 16], 
[2,5,8,10,12,14,16,20,21,22,23,24,25,27,29,31,34,36,37,40,43,44,47,50,51,54,59,60,61,62,65,72,73,74,75,76,77,78,81,83,86,88,90,92,94,97,98,99,101,105,107,109,113,117,120,124,125,126,127,128,129,130,131,133,135,136,138,139,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,165,166,167,169,171,172,173,175,177,179,181,183,188,193,195,197,198,199,201,203,204,206,208,212,213,214,215,220,222,224,226,229,231,233,236,239,242,245,249,251,254,257,258,261,264,269,274,276,278,280,282,284,287,291,297,298,300,301,303,307,308,309,310,311,312,313,314,315,316,317,318,319,320,323,326,327,328,330,332,334,335,337,339,341,343,345,346,347,348,350,352,353,355,356,358,367,368,369,370,371,372,373,374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 387, 392, 394, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 413, 414, 415, 419, 423, 424, 425, 426, 428, 430, 432, 434, 437, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 462, 465, 467, 469, 472, 474, 476, 479, 481, 483, 486, 488, 490, 492, 494, 496, 499, 501, 503, 506, 508, 509, 511, 512, 514, 517, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 534, 537, 538, 539, 540, 541, 543, 545, 550, 555, 557, 559, 561, 563, 566, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 584, 586, 588, 590, 593, 595, 597, 600, 602, 604, 607, 609, 613, 616, 617, 620, 628, 631, 633, 636, 638, 640, 642, 644, 645, 646, 649, 650, 652, 654, 656, 658, 660, 661, 663, 664, 665, 666, 667, 669, 671, 674, 676, 679, 680, 682, 683, 685, 689, 691, 694, 697, 700, 703, 707, 709, 712, 715, 717, 727, 735, 743, 747, 752, 754, 756, 758, 760, 763, 773],
[2,3,4,5,6,7,8,9,10,11,12,13,14,16,18,19,20,22,23,24,25,26,28,30,31,33,34,35,36,38,42,44,48,52,56,61,65,69,73,78,82,86,90,97,],

[2,5,7,8,10,12,14,16,19,22,25,28,31,34,37,40,43,46,48,50,51,53,54,56,57,59,60,62,63,65,66,68,69,71,72,74,75,77,78,80,81,83,85,87,88,89,90,92,93,95,96,98,99,100,101,102,103,104,105,106,107,108,111,115,117,119,121,123,],
[2,3,4,5,7,8,9,10,11,12,13,15,17,19,20,21,22,25,29,30,33,35,36,37,38,39,40,42,43,44,46,47,49,51,53,55,],
[2,4,6,8,10,13,14,15,16,18,20,22,23,24,25,26,27,28,31,34,35,37,38,40,41,42,44,46,48,49,51,53,57,59,61,63,64,66,68,69,71,72,73,74,75,76,79,81,82,84,86,], 
[2,3,4,5,6,7,8,10,12,14,16,17,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,53,54,56,58,59,60,62,64,66,68,70,72,73,74,75,76,78,79,81,82,84,87,88,89,90,91,93,95,97,99,101,103,105,107,109,110,111,112,113,115,117,119,121,123,125,127,129,131,133,135,137,139,140,141,143,147,148,154,156,158,162,163,166,168,170,171,173,174,176,177,179,180,182,183,185,186,188,189,191,192,194,195,197,198,200,201,203,205,208,211,212,213,215,216,218,220,222,225,229,231,233,235,238,240,242,244,246,248,251,254,256,260,261,262,263,264,265,266,267,268,270,272,274,276,277,278,280,281,282,283,284,286,289,291,294,297,299,302,303,],

][5:]

# idx = projects.index(prj)
# funcs = returnses[idx]
# print(len(funcs))
# with open('rerrr', 'w+') as f:
#     returnses[-1] = [x-1 for x in returnses[-1]]
#     f.write(str(returnses[-1])) 
model = 'TW'
lower = True
check_ret = False
mass_object = True
mass_container = True
ignore_no_res = False
ignore_ground_no_return = False
all_precisions = 0
all_recalls = 0
all_f1s = 0
all_cnt = 0
mrrs = 0
no_match_ground = []

def pure(typ):
    typ = typ.replace('*','').replace('?','')
    if typ.startswith('optional[') and typ.endswith(']'):
        typ = typ[9:-1]
    # if typ.startswith('Optional[') and typ.endswith(']'):
    #     typ = typ[9:-1]
    
    return typ
models = ['pytype', 'typilus', 'TW', 'PIG']
# models = ['PIG']
P = defaultdict(list)
R = defaultdict(list)
F1 = defaultdict(list)
MRR = defaultdict(list)
model = 'TW'
for k in [1,3]:
    for ii, project in enumerate(projects):
        for model in models:
        # if i == 4:
        #     lower = False
            print(model + '---' + project)
            print('----------------------')
            ground_truth = []
            returns = returnses[ii]
            with open(f'evaluation/GT_{project}.txt') as f:
                
                for i, line in enumerate(f):
                    if i == 0:
                        continue
                    if lower:
                        line = line.lower()
                    ground_truth.append(line.strip().split('/'))
            PIG = []
            with open(f'evaluation/{model}_{project}.txt') as f:
                
                for i, line in enumerate(f):
                    if i == 0:
                        continue
                    if lower:
                        line = line.lower()
                    qualifier_names = line.strip().split('/')
                    PIG.append([pure(x.replace('typing.','').split('.')[-1]) for x in qualifier_names])
            precisions = 0
            recalls = 0
            f1s = 0
            cnt = 0
            mrrs = 0
            def remove_nan(p):
                return [x for x in p if x  != 'nan']
            def remove_none(p):
                return [x for x in p if x  != 'none']
            def remove_any(p):
                return [x for x in p if x  != 'any']

            
            ds = ['list','set','tuple','dict']
            def same_ds(x, g):
                if not mass_container:
                    return False
                if x == 'object':
                    return True
                for d in ds:
                    if x.find(d) != -1:
                        for g_ in g:
                            if g_.find(d) != -1:
                                return True

                return False

            def same_type_recall(g, p):
                if g == 'any':
                    return True
                if mass_object and  g == 'object':
                    return True
                if g in p:
                    return True

            def compatible(x,y):
                # x<:y, since x should be valid if its a subtype of y  
                if x == y:
                    return True

                if y == 'int':
                    if x =='bool':
                        return True
                if y == 'float':
                    if x =='int':
                        return True
                    if x =='bool':
                        return True
                
                if y == 'any' or y == 'object':
                    return True
                

            def coherent(x,y):
                # x<:y, since x should be valid if its a subtype of y  
                if x == y:
                    return True

                if y == 'bool':
                    return True

            def alias(x, y):
                if x == y:
                    return True
                if x == 'numpy.ndarray[Any, Any]' and y == 'ndarray':
                    return True
                if y == 'numpy.ndarray[Any, Any]' and x == 'ndarray':
                    return True
                if x == 'numpy.ndarray[Any, numpy.dtype[numpy.floating[numpy.typing._64Bit]]]' and y == 'ndarray':
                    return True
                if y == 'numpy.ndarray[Any, numpy.dtype[numpy.floating[numpy.typing._64Bit]]]' and x == 'ndarray':
                    return True
                
                
                
            def same_type(x, g):

                if x in g:
                    return True

                # if 'bool' in g:
                #     if x == 'int':
                #         return True
                #     if x == 'float':
                #         return True
                    
                # if 'int' in g :
                #     if x == 'float':
                #         return True
                #     if x == 'bool':
                #         return True

                # if x.find('literal') != -1:
                #     if 'int' in g:
                #         return True
                #     if 'str' in g:
                #         return True
                if 'any' in g:
                    return True

                if mass_object and 'object' in g:
                    return True
                # if 'bool' in g and ('float' == x or 'int' == x or 'object' == x):
                #     return True
                # if 'int' in g and ('float' == x):
                #     return True
                # if 'float' in g and ('int' == x):
                #     return True
                
                # if x == 'object':
                #     return True
                # for d in ds:
                #     if x.find(d) != -1:
                #         for g_ in g:
                #             if g_.find(d) != -1:
                #                 return True

                return False

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

                if len(p) == 1 and p[0]=='':
                    p = []
                p = remove_nan(p)
                if model != 'pytype':
                    p = remove_any(p)
                p = p[:k]
                if check_ret:
                    b = i + 2 in returns
                else:
                    b = i + 2 not in returns
                if b:
                    
                    g = ground_truth[i]
                    if 'any' in g:
                        continue
                    if len(g) == 1 and g[0]=='':
                        continue
                    
                    
                    if ignore_ground_no_return and 'none' in g:
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
                        hit_accuracy = sum([same_type(x, g) or same_ds(x, g) for x in p])
                        if hit_accuracy > 0:
                            pass

                            # print(i)
                        hit_recall = sum([same_type_recall(x, p) or same_ds(x, p) for x in g])
                        mrr = calc_mrr(p, g)
                        # with open('xxx', 'a+') as f:

                        #     f.write(str(i) + ' ' + str(hit_accuracy)+'\n')
                        # if not hit_accuracy and p[0]!='any':
                        #     # print(i)
                        #     no_match_ground.append((project, i, p ,g))
                        #     c +=1
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
                print(precisions/cnt)
                print(recalls/cnt)
                print(f1s/cnt)
                print(mrrs/cnt)
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
                    
                else:
                    P[k].append('{:.2f}'.format(round(precisions/cnt, 2)))
                    R[k].append('{:.2f}'.format(round(recalls/cnt, 2)))
                    F1[k].append('{:.2f}'.format(round(f1s/cnt, 2)))
                    
            all_precisions += precisions
            all_recalls += recalls
            all_f1s += f1s
            all_cnt += cnt
            


with open('table.txt', 'w+') as f:

    f.write('$P_1$ & ' + ' & '.join(P[1]) + '\\\\ \\hline' +'\n')
    f.write('$R_1$ & ' + ' & '.join(R[1]) + '\\\\ \\hline' +'\n')
    f.write('$F1_1$ & ' + ' & '.join(F1[1])+ '\\\\ \\hline' +'\n')
    # f.write('$MRR_1$ & ' + ' & '.join(MRR[1])+ '\\\\ \\hline' +'\n')
    
    f.write('$P_3$ & ' + ' & '.join(P[3]) + '\\\\ \\hline' +'\n')
    f.write('$R_3$ & ' + ' & '.join(R[3]) + '\\\\ \\hline' +'\n')
    f.write('$F1_3$ & ' + ' & '.join(F1[3])+ '\\\\ \\hline' +'\n')
    # f.write('$MRR_3$ & ' + ' & '.join(MRR[3])+ '\\\\ \\hline' +'\n')
    

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
