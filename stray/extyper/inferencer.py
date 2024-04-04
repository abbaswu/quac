from collections import defaultdict
from copy import copy
from gc import collect
import itertools
import fnmatch
import eventlet
from contextlib import contextmanager
import time
from datetime import datetime
from typing import (
    Any, Dict, Set, List, cast, Tuple, TypeVar, Union, Optional, NamedTuple, Iterator,
    Iterable, Sequence, Mapping, Generic, AbstractSet, Callable
)
from typing_extensions import Final
from extyper.errors import Errors, report_internal_error
from extyper.nodes import (
    UNBOUND_IMPORTED, Argument, FlowNode, SymbolTable, Statement, MypyFile, Var, Expression, Lvalue, Node,
    OverloadedFuncDef, FuncDef, FuncItem, FuncBase, TypeInfo,
    ClassDef, Block, AssignmentStmt, NameExpr, MemberExpr, IndexExpr,
    TupleExpr, ListExpr, ExpressionStmt, ReturnStmt, IfStmt,
    WhileStmt, OperatorAssignmentStmt, WithStmt, AssertStmt,
    RaiseStmt, TryStmt, ForStmt, DelStmt, CallExpr, IntExpr, StrExpr,
    UnicodeExpr, OpExpr, UnaryExpr, LambdaExpr, TempNode, SymbolTableNode,
    Context, Decorator, PrintStmt, BreakStmt, PassStmt, ContinueStmt,
    ComparisonExpr, StarExpr, EllipsisExpr, RefExpr, PromoteExpr,
    Import, ImportFrom, ImportAll, ImportBase, TypeAlias,
    ARG_POS, ARG_STAR, LITERAL_TYPE, LDEF, MDEF, GDEF,
    CONTRAVARIANT, COVARIANT, INVARIANT, TypeVarExpr, AssignmentExpr,
    is_final_node,
    ARG_NAMED)
from extyper import nodes
from extyper import operators
from extyper.literals import literal, literal_hash, Key
from extyper.typeanal import has_any_from_unimported_type, check_for_explicit_any, make_optional_type
from extyper.types import (
    Type, AnyType, CallableType, FunctionLike, Overloaded, TupleType, TypedDictType,
    Instance, NoneType, strip_type, TypeType, TypeOfAny,
    UnionType, TypeVarId, TypeVarType, PartialType, DeletedType, UninhabitedType,
    is_named_instance, union_items, TypeQuery, LiteralType, MaybeTypes,
    is_optional, remove_optional, TypeTranslator, StarType, get_proper_type, ProperType,
    get_proper_types, is_literal_type, TypeAliasType, TypeGuardedType)
from extyper.sametypes import is_same_type
from extyper.messages import (
    MessageBuilder, make_inferred_type_note, append_invariance_notes, pretty_seq,
    format_type, format_type_bare, format_type_distinctly, SUGGESTED_TEST_FIXTURES
)
import extyper.inferexpr
from extyper.inferexpr import get_ground_pairs
from extyper.checkmember import (
    analyze_member_access, analyze_descriptor_access, type_object_type, lookup_member_var_or_accessor
)
from extyper.typeops import (
    map_type_from_supertype, bind_self, erase_to_bound, make_simplified_union,
    erase_def_to_union_or_bound, erase_to_union_or_bound, coerce_to_literal,
    try_getting_str_literals_from_type, try_getting_int_literals_from_type,
    tuple_fallback, is_singleton_type, try_expanding_enum_to_union,
    true_only, false_only, function_type, get_type_vars, custom_special_method,
    is_literal_type_like,
)
from extyper import message_registry
from extyper.subtypes import (
    is_subtype, is_equivalent, is_proper_subtype, is_more_precise,
    restrict_subtype_away, is_subtype_ignoring_tvars, is_callable_compatible,
    unify_generic_callable, find_member
)
from extyper.constraints import SUPERTYPE_OF
from extyper.maptype import map_instance_to_supertype
from extyper.typevars import fill_typevars, has_no_typevars, fill_typevars_with_any
from extyper.semanal import set_callable_name, refers_to_fullname
from extyper.mro import calculate_mro, MroError
from extyper.erasetype import erase_typevars, remove_instance_last_known_values, erase_type
from extyper.expandtype import expand_type, expand_type_by_instance
from extyper.visitor import NodeVisitor
from extyper.join import is_similar_callables, join_types, object_from_instance, object_or_any_from_type
from extyper.treetransform import TransformVisitor
from extyper.binder import ConditionalTypeBinder, get_declaration
from extyper.meet import is_overlapping_erased_types, is_overlapping_types
from extyper.options import Options
from extyper.plugin import Plugin, CheckerPluginInterface
from extyper.sharedparse import BINARY_MAGIC_METHODS
from extyper.scope import Scope
from extyper import state, errorcodes as codes
from extyper.traverser import has_return_statement, all_return_statements
from extyper.errorcodes import ErrorCode
from extyper.util import is_typeshed_file


USE_PCT = False # We prefer sort parameters by the size of their type seeds now, which actually make PCT useless

T = TypeVar('T')
DEFAULT_LAST_PASS: Final = 1  
DeferredNodeType = Union[FuncDef, LambdaExpr, OverloadedFuncDef, Decorator]
FineGrainedDeferredNodeType = Union[FuncDef, MypyFile, OverloadedFuncDef]
DeferredNode = NamedTuple(
    'DeferredNode',
    [
        ('node', DeferredNodeType),
        ('active_typeinfo', Optional[TypeInfo]),  
    ])
FineGrainedDeferredNode = NamedTuple(
    'FineGrainedDeferredNode',
    [
        ('node', FineGrainedDeferredNodeType),
        ('active_typeinfo', Optional[TypeInfo]),
    ])
TypeMap = Optional[Dict[Expression, Type]]
TypeRange = NamedTuple(
    'TypeRange',
    [
        ('item', Type),
        ('is_upper_bound', bool),  
    ])
PartialTypeScope = NamedTuple('PartialTypeScope', [('map', Dict[Var, Context]),
                                                   ('is_function', bool),
                                                   ('is_local', bool),
                                                   ])
class TypeInferencer(NodeVisitor[None], CheckerPluginInterface):
    """Mypy type checker.
    Type check mypy source files that have been semantically analyzed.
    You must create a separate instance for each source file.
    """
    is_stub = False
    errors: Errors
    msg: MessageBuilder
    type_map: Dict[Expression, Type]
    wide_type_map: Dict[Expression, Type]
    binder: ConditionalTypeBinder
    expr_checker: extyper.inferexpr.ExpressionInferencer
    tscope: Scope
    scope: "CheckerScope"
    return_types: List[Type]
    partial_types: List[PartialTypeScope]
    partial_reported: Set[Var]
    globals: SymbolTable
    modules: Dict[str, MypyFile]
    deferred_nodes: List[DeferredNode]
    pass_num = 0
    last_pass = DEFAULT_LAST_PASS
    current_node_deferred = False
    is_typeshed_stub = False
    suppress_none_errors = False  
    options: Options
    no_partial_types: bool = False
    module_refs: Set[str]
    var_decl_frames: Dict[Var, Set[int]]
    plugin: Plugin
    def __init__(self, errors: Errors, modules: Dict[str, MypyFile], options: Options,
                 tree: MypyFile, path: str, plugin: Plugin, union_errors=None, incompatible=None, single_incompatible=None, infer_dependency_map=None, manager=None, added_attr=None, func_name_recorder = None, func_name_order=None, 
                 func_s1=None, func_s2=None, func_s3=None, func_finished=None, func_candidates=None, func_must=None, func_class=None) -> None:
        """Construct a type checker.
        Use errors to report type check errors.
        """
        self.errors = errors
        self.modules = modules
        self.options = options
        self.tree = tree
        self.path = path
        self.msg = MessageBuilder(errors, modules)
        self.plugin = plugin
        self.union_errors = union_errors
        self.incompatible = incompatible
        self.single_incompatible = single_incompatible
        self.added_attr = added_attr
        self.check_dependency_map = {}
        self.infer_dependency_map = infer_dependency_map
        self.func_s1 = func_s1
        self.func_s2 = func_s2
        self.func_s3 = func_s3 
        self.func_must = func_must
        self.mode = 'PTI'
        self.combination_limits = 4096
        self.func_seeds = {}
        self.manager = manager
        self.scope = CheckerScope(tree)
        self.msg.errors.cscope = self.scope
        self.message = set()
        self.improvement = set()
        self.tv_level = defaultdict(list)
        self.arg_level = {}
        self.record = {}
        self.added_attr = set()
        self.func_candidates = func_candidates
        self.must_analyze = {}
        self.func_finished = func_finished
        self.func_orderred_type = defaultdict(dict)
        self.func_class = func_class
        self.global_vars = set()
        self.expr_checker = extyper.inferexpr.ExpressionInferencer(self, self.msg, self.plugin, union_errors, incompatible, single_incompatible, self.infer_dependency_map, self.added_attr, self.message)
        self.tscope = Scope()
        self.var_type = {}
        self.type_hook = {}
        self.method_typing = {}
        self.globals = tree.names
        tree.path.replace('/', '-')
        self.result_file = open('result/' + tree.path.replace('/', '-') +'_whole_', 'w+')
        self.result_file.close()
        self.result_file2 = open('result/' + tree.path.replace('/', '-') +'_orderred_', 'w+')
        self.result_file2.close()
        self.result_file = open('result/' + tree.path.replace('/', '-') +'_whole_', 'a+')
        self.result_file2 = open('result/' + tree.path.replace('/', '-') +'_orderred_', 'a+')
        self.union_context = None
        self.return_types = []
        self.partial_types = []
        self.partial_reported = set()
        self.var_decl_frames = {}
        self.deferred_nodes = []
        self.type_map = {} 
        self.var_node = {} 
        self.binder = ConditionalTypeBinder(self) 
        self.wide_type_map = {}
        self.dp_dag = {}
        self.cache_type_map = {}
        self.module_refs = set()
        self.pass_num = 0
        self.current_node_deferred = False
        self.is_stub = tree.is_stub
        self.is_typeshed_stub = is_typeshed_file(path)
        self.inferred_attribute_types = None
        if options.strict_optional_whitelist is None:
            self.suppress_none_errors = not options.show_none_errors
        else:
            self.suppress_none_errors = not any(fnmatch.fnmatch(path, pattern)
                                                for pattern
                                                in options.strict_optional_whitelist)
        self.recurse_into_functions = True
        self._is_final_def = False
        self.node = None
        self.err_cnts = 0
        self.is_checking = False
        self.func_name_recorder = func_name_recorder
        self.func_name_order = func_name_order
    def update_infer_dependency_map(self, a, b):
        if a not in self.infer_dependency_map:
            self.infer_dependency_map[a] = []
        if len(b) > 0 and b not in self.infer_dependency_map[a]:
            self.infer_dependency_map[a].append(b)
    def update_infer_dependency_map_multiple_values(self, pair1, r_identity, typs):
        typs = list(set(typs))
        if pair1 not in self.infer_dependency_map:
            self.infer_dependency_map[pair1] = []
        for typ in typs:
            self.infer_dependency_map[pair1].append([(r_identity, typ)])
    def update_check_dependency_map(self, a, b):
        if self.check_dependency_map.get(a, None) is None:
            self.check_dependency_map[a] = []
        self.check_dependency_map[a].append(b)
    @property
    def type_context(self) -> List[Optional[Type]]:
        return self.expr_checker.type_context
    def reset(self) -> None:
        """Cleanup stale state that might be left over from a typechecking run.
        This allows us to reuse TypeChecker objects in fine-grained
        incremental mode.
        """
        self.partial_reported.clear()
        self.module_refs.clear()
        self.binder = ConditionalTypeBinder(self)
        self.expr_checker.local_infer_map.clear()
        self.infer_dependency_map.clear()
        assert self.deferred_nodes == []
        assert len(self.scope.stack) == 1
    def get_trivial_type(self, fdef: FuncDef) -> CallableType:
        return CallableType(
            [AnyType(TypeOfAny.suggestion_engine) for a in fdef.arg_kinds],
            fdef.arg_kinds,
            fdef.arg_names,
            AnyType(TypeOfAny.suggestion_engine),
            self.manager.semantic_analyzer.builtin_type('builtins.function'))
    def contains_all(self, items, state):
        return all(item in state for item in items if items[0] is not None)
    def get_starting_type(self, fdef: FuncDef) -> CallableType:
        return self.get_trivial_type(fdef)
    def all_type(self):
        return self.candidates
    def suggest_class(self, cld: ClassDef, init=False):
        self.manager.lexical_stat[type(cld)].add(cld)
        with self.tscope.class_scope(cld.info):
            old_binder = self.binder
            self.binder = ConditionalTypeBinder(self)
            with self.binder.top_frame_context():
                with self.scope.push_class(cld.info):
                    b = cld.defs
                    self.none_global = set()
                    self.class_vars = set()
                    self.global_single_incompatible = {}
                    self.global_incompatible = {}
                    self.func_solutions = {}
                    all_success = True
                    for s in b.body:
                        if self.binder.is_unreachable():
                            break
                        if isinstance(s, FuncDef):
                            print(s.name)
                            if self.mode == 'CPA':
                                self.suggest_function_CPA(s,True, init=init)
                            else:
                                self.suggest_function(s,True, init=init)
                        elif isinstance(s, Decorator):
                            if self.mode == 'CPA':
                                self.suggest_function_CPA(s.func,True)
                            else:
                                self.suggest_function(s.func,True, init=init)
                        elif isinstance(s, AssignmentStmt):
                            self.visit_assignment_stmt(s)
                        else:
                            self.accept(s)
                    if all_success:
                        pass
                    else:
                        self.defer_node(cld, cld.info)
        self.binder = old_binder
    def merge_function(self, func):
        if func.type is not None:
            return
        worklist = self.func_solutions[func]
        base = self.get_starting_type(func)
        args = [x for x in func.arguments]
        solutions = []
        args2ann = {}
        for w in worklist:
            if self.fine(w, self.final_global):
                r_args = self.project(w, to=args)
                ann = self.to_annotation(base, w, args)
                if r_args not in args2ann:
                    args2ann[r_args] = ann
                    if ann not in solutions:
                        solutions.append(ann)
        if len(solutions) == 0:
            solutions.append(base)
        mu_def = Overloaded(solutions)
        func.type = mu_def
    def fine(self, w, solution):
        if isinstance(solution, list) and isinstance(solution[0], tuple):
            solutions = solution
            for solution in solutions:
                corrects = set()
                w = w[1:]
                s = solution[1:]
                s_nodes_type = {x[0]:x[1] for x in s}
                for pair in w:
                    node, typ = pair
                    if node in s_nodes_type:
                        node_t = s_nodes_type[node]
                        if is_subtype(node_t, typ) or is_subtype(typ, node_t):  
                            corrects.add(True)
                        else:
                            corrects.add(False)
                            break
                    else:
                        corrects.add(True)
                if all(corrects):
                    return True
            return False
        corrects = set()
        w = w[1:]
        s = solution[1:]
        s_nodes_type = {x[0]:x[1] for x in s}
        for pair in w:
            node, typ = pair
            if node in s_nodes_type:
                node_t = s_nodes_type[node]
                if is_subtype(node_t, typ) or is_subtype(typ, node_t):  
                    corrects.add(True)
                else:
                    corrects.add(False)
                    break
            else:
                corrects.add(True)
        if all(corrects):
            return True
        return all(corrects)
    def fine_single(self, w, final_candidates):
        for node, typ in w[1:]:
            if node in self.class_vars:
                if typ not in final_candidates[node]:
                    return False
        return True
    def merge_by_concat(self):
        def exists(T, t):
            for x in T:
                if is_subtype(t, x) or is_subtype(x, t):
                    return True
            return False
        def merge(w, solution):
            w = tuple(w)
            solution = tuple(solution)
            new_solution = {}
            for pair in w[1:] + solution[1:]:
                node, typ = pair
                if node in new_solution:
                    previous_typ = new_solution[node]
                    if is_subtype(typ, previous_typ): 
                        new_solution[node] = typ
                else:
                    new_solution[node] = typ
            new_solution = set(new_solution.items())
            new_solution = [x for x in new_solution if x[0] in self.class_vars]
            ret = ['start'] + new_solution
            return tuple(ret)
        worklist = [['start']]
        func_candidates = defaultdict(list)
        type_candidates = defaultdict(set)
        for solutions in self.func_solutions.values():
            single_candidates = defaultdict(set)
            for solution in solutions:
                for node, typ in solution[1:]:
                    if node in self.class_vars:
                        single_candidates[node].add(typ)
                        type_candidates[node].add(typ)
            for node in single_candidates:
                func_candidates[node].append(single_candidates[node])
        final_candidates = defaultdict(set)
        for node in func_candidates:
            for t in type_candidates[node]:
                ok = all([exists(TT, t) for TT in func_candidates[node]])
                if ok:
                    final_candidates[node].add(t)
        solutions_list = self.func_solutions.values()
        solutions_list = sorted(solutions_list, key = lambda x: len(x))
        for solutions in solutions_list:
            new_worklist = set()
            for w in worklist:
                if self.fine_single(w, final_candidates):
                    for solution in solutions:
                        if self.fine_single(solution, final_candidates):
                            if self.fine(w, solution):
                                nw = merge(w, solution)
                                new_worklist.add(nw)
            worklist = new_worklist
        if len(worklist) >= 1:
            self.final_global = list(worklist)
            for global_pairs in self.final_global[0][1:]:
                node, typ = global_pairs
                if isinstance(node, NameExpr):
                    node.node.type = typ
                    node.node.is_ready = True
        else:
            self.final_global = [['start']]
    def suggest_assignment(self, s, from_class=False):
        node = None
        lvalues = s.lvalues
        if len(lvalues) == 1 and isinstance(lvalues[0], NameExpr):
            node = lvalues[0]
            if from_class:
                self.class_vars.add(node)
            else:
                self.global_vars.add(node)
            if hasattr(s.rvalue, "name") and s.rvalue.name == 'None':
                pass
            var = node.node
            if s.type:
                self.store_type(node, [s.type], overwrite=True)
                self.update_var_node(node)
            else:
                if node not in self.type_map:
                    self.store_type(node, self.S1(), overwrite=True)
                    self.update_var_node(node)
                    self.accept(s)
                else:
                    pass 
        if node is None:
            return True
        worklist = [['start']]
        typs = self.type_map[node]
        new_worklist = []
        for typ in typs:
            for state in worklist:
                new_state = [x for x in state]
                new_state.append((node, typ))
                new_worklist.append(new_state)
        worklist = new_worklist
        if from_class:
            self.func_solutions[s]=(worklist)
    def to_annotations(self, base, wlist, args):
        solutions = set()
        for w in wlist:
            solution = self.to_annotation(base, w, args)
            solutions.add(solution)
        ann = Overloaded(solution)
        return ann
    def to_annotation(self, base, w, args):
        def maybe_degenerate(t, r):
            if isinstance(t, TypeVarType):
                if isinstance(r, TypeVarType):
                    if t == r:
                        return t
                else:
                    if isinstance(r, Instance):
                        if t in r.args:
                            return t
                    if isinstance(r, TupleType):
                        if t in r.items:
                            return t
                return object_or_any_from_type(t)
            else:
                return t
        arg_list = []
        for arg in args:
            ok = False
            for node, typ in w[1:-1]:
                if node == arg:
                    arg_list.append(maybe_degenerate(typ, w[-1][1]))
                    ok = True
                    break
            if not ok:
                arg_list.append(AnyType(100))
        variables = []
        for at in arg_list:
            if isinstance(at, TypeVarType):
                variables.append(at)
            else:
                if isinstance(at, Instance):
                    for a in at.args:
                        if isinstance(a, TypeVarType):
                            variables.append(a)            
        now = base.copy_modified(arg_types=arg_list, ret_type=w[-1][1], variables=variables)
        return now
    def project(self, solution, to=None, global_=False):
        if to:
            new_solution = [x for x in solution if x[0] in to]
        else:
            if global_:
                new_solution = [x for x in solution if x[0] in self.class_vars]
            else:    
                new_solution = [x for x in solution if x[0] not in self.class_vars]
        return tuple(new_solution)
    def same_solutions(self, s1, s2):
        if len(s1) != len(s2):
            return False
        for s in s1:
            if s not in s2:
                return False
        return True
    def try_expand(self, base, worklist, args):
        worklist = set([tuple(x) for x in worklist])
        arg2ann = {}
        for w in worklist:
            r_args = self.project(w, to=args)
            ann = self.to_annotation(base, w, args)
            if r_args not in arg2ann:
                arg2ann[r_args] = ann
        return arg2ann
    def try_reduce(self, base, worklist, args):
        worklist = set([tuple(x) for x in worklist])
        arg2ann = {}
        for w in worklist:
            args_global = self.project(w, global_=True)
            ann = self.to_annotation(base, w, args)
            if args_global in arg2ann:
                arg2ann[args_global].add(ann)
            else:
                arg2ann[args_global] = set([ann])
        annos = [x for x in arg2ann.values()]
        if all([self.same_solutions(x, annos[0]) for x in annos]):
            return True, arg2ann
        else:
            return False, arg2ann
    def global_solving(self):
        def get_candidates(x):
            if isinstance(x, (set, list)):
                return len(x)
            else:
                return 1
        grounds = []
        for var in self.wide_type_map:
            flag = 0
            for var2, typ in self.expr_checker.local_infer_map:
                if var2 == var:
                    source_pairss = self.expr_checker.local_infer_map[(var2, typ)]
                    source_nodes = []
                    for source_pairs in source_pairss:
                        source_nodes.extend([x[0] for x in source_pairs])
                    if not all(isinstance(x, FlowNode) for x in source_nodes):
                        flag = 1
                        break
            if flag == 0 and var not in grounds:
                grounds.append(var)
        grounds = sorted(grounds, key=lambda x:get_candidates(self.wide_type_map[x]))
        single_incompatible1 = self.single_incompatible
        double_incompatible = self.incompatible
        worklist = [['start']]
        updates = []
        for g in grounds:
            new_worklist = []
            types = self.wide_type_map[g]
            for typ in types:
                id_pair = (g, typ)
                if not (g in single_incompatible1 and typ in single_incompatible1[g]):
                    for state in worklist:
                        if (id_pair not in double_incompatible) or (not any([self.contains_all(x, state) for x in double_incompatible[id_pair]])):
                            new_state = [x for x in state]
                            new_state.append(id_pair)
                            new_worklist.append(new_state)  
            if len(new_worklist) == 0:
                updates.append(g)
                for typ in types:
                    id_pair = (g, typ)
                    if id_pair in double_incompatible:
                        for p in double_incompatible[id_pair]:
                            for x in p:
                                updates.append(x[0])
                worklist = new_worklist
                break
            worklist = new_worklist
        return worklist, set(updates)
    def init_candidates(self, node):
        nows = {}
        now = self.S3(node)
        for arg in node.arguments:
            nows[arg] = copy(now)
        return nows
    def suggest_function_CPA_(self, node, from_class = False, force=False):
        def improve(a, t):
            if isinstance(t, TypeVarType):
                if 'T' in self.tv_level[a]:
                    return None
                else:
                    self.tv_level[a].append('T')
                    return set(self.S2(self.func_candidates[node], ground=a))
            else:
                if t.type.fullname in self.tv_level[a]:
                    return None
                else:  
                    self.tv_level[a].append(t.type.fullname)
                    return self.S3_for(t)
        def improvement():
            success = False
            for (a, t) in self.improvement:
                if a in nows:
                    now = set(nows[a])
                    ret = improve(a, t)
                    if ret is not None:
                        now.update(ret)
                        nows[a] = list(now)
                        success = True
            return success
        def try_to_update(updates):
            unsolvable = False
            hit = False
            for ground in updates:
                if ground in nows:
                    hit = True
                    now = nows[ground]
                    if now == self.S1(self.func_candidates[node], ground):
                        now = self.S2(self.func_candidates[node], ground)
                    elif now == self.S2(self.func_candidates[node], ground):
                        now = self.S3(self.func_candidates[node], ground)
                    else:
                        unsolvable = True
                    nows[ground] = now
                elif hasattr(self, "class_vars") and ground in self.class_vars:
                    hit = True
                    if ground not in self.none_global:
                        self.type_map[ground] = self.makeS4Type(self.type_map[ground])
                    else:
                        if self.type_map[ground].items == self.S1():
                            self.type_map[ground] = self.makeS2Type()
                        elif self.type_map[ground].items == self.S2():
                            self.type_map[ground] = self.makeS3Type()
                        elif self.type_map[ground].items == self.S3():
                            self.type_map[ground] = self.makeS4Type()
                        else:
                            unsolvable = True
            return not(not hit or unsolvable)
        def add_attr(x, attrs):
            candidates = self.s2 + self.s3
            for candidate in candidates:
                candidate_info = candidate.type
                retrieve_attr_res = [candidate_info.get(x) for x in attrs]
                if all([x is not None for x in retrieve_attr_res]):
                    if candidate not in x:
                        list_user_type = self.type_checker().named_type_with_type_var('builtins.list', candidate)
                        set_user_type = self.type_checker().named_type_with_type_var('builtins.set', candidate)
                        x.append(candidate)
                        x.append(list_user_type)
                        x.append(set_user_type)
            return x
        def add_type(x, types):
            for typ in types:
                if typ not in x:
                    x.append(x)
            return x
        if node.unanalyzed_type is not None:
            return
        node.type = None
        func_name = node.fullname
        line_no = node.line
        is_method = bool(node.info) and not node.is_static
        base = self.get_starting_type(node)
        if node not in self.func_class:
            if bool(node.info):
                self.func_class[node] = node.info
            else:
                self.func_class[node] = None
        nows = {}
        self.record = {}
        for arg in node.arguments:
            nows[arg] = self.S2(ground = arg)
            self.arg_level[arg] = 1
        original_var_node = {k:v for k,v in self.var_node.items()}
        original_type_map = {k:v for k, v in self.type_map.items()}
        original_wide_type_map = {k:v for k, v in self.wide_type_map.items()}
        original_infer_map = {k:v for k,v in self.expr_checker.local_infer_map.items()}
        original_dp_dag = {k:v for k,v in self.dp_dag.items()}
        list_now = []
        for i in range(len(base.arg_kinds)):
            argument = node.arguments[i]
            list_now.append(nows[argument])
        combinations = itertools.product(*list_now)
        solutions = []
        start = time.time()
        flag = 0
        for combination in combinations:
            annots = []
            for i in range(len(base.arg_kinds)):
                argument = node.arguments[i]
                typ = combination[i]
                if i == 0 and is_method:
                    annots.append(Instance(node.info, [AnyType(TypeOfAny.from_omitted_generics)] * len(node.info.defn.type_vars)))
                else:
                    annots.append(typ)
            node.type = base.copy_modified(arg_types=annots)
            func = node
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.cache_type_map.clear()
            self.defer_this_node = False        
            self.infer_dependency_map = {}
            self.single_incompatible.clear()
            self.incompatible.clear()
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.added_attr.clear()
            self.message.clear()
            self.improvement.clear()
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            grounds = []
            self.expr_checker.timeout = False
            self.visit_func_def(node)
            if self.defer_this_node:
                break
            else:
                worklist, updates = self.global_solving()
                if len(worklist) > 0:
                    new_worklist = []
                    none_type = NoneType()
                    ret_node = TempNode(none_type)
                    for w in worklist:
                        phi_ret = []
                        if len(self.infer_dependency_map) == 0:
                            pass
                        elif len(self.infer_dependency_map) == 1 and all([len(x) == 0 for x in self.infer_dependency_map.values()]):
                            for node_, typ in self.infer_dependency_map:
                                phi_ret.append(typ)
                        else:
                            for node_, typ in self.infer_dependency_map:
                                if len(self.infer_dependency_map[(node_, typ)]) == 0:
                                    phi_ret.append(typ)
                                else:
                                    for possiblity in self.infer_dependency_map[(node_, typ)]:
                                        if self.contains_all(possiblity, w):
                                            phi_ret.append(typ)
                                            break
                                        else:
                                            pass
                        if len(phi_ret) > 1:
                            phi_ret = UnionType.make_union(phi_ret)
                        elif len(phi_ret) == 1:
                            phi_ret = phi_ret[0]
                        else:
                            if len(self.infer_dependency_map) == 0:
                                phi_ret = NoneType(0)
                            else:
                                phi_ret = UnionType.make_union([x[1] for x in self.infer_dependency_map.keys()])
                        if not isinstance(phi_ret, NoneType):
                            try:
                                w.append((node_, phi_ret))
                                new_worklist.append(w)
                            except Exception:
                                pass
                        else:
                            w.append((ret_node, none_type))
                            new_worklist.append(w)
                        self.infer_dependency_map.clear()
                        worklist = new_worklist
                        args = [x for x in func.arguments]
                        if not from_class:
                            for w in worklist:
                                ann = self.to_annotation(base, w, args)
                                if ann not in solutions:
                                    solutions.append(ann)
                        else:
                            self.func_solutions[func] = worklist
                            reduce, args2ann = self.try_reduce(base, worklist, args)
                            reduce = True
                            if reduce:
                                if len(args2ann) == 0:
                                    func.type = base
                                else:
                                    ftype = Overloaded(list(list(args2ann.values())[0]))
                                    solutions.extend(list(list(args2ann.values())[0]))
                                    func.type = ftype
                            else:
                                self.method_typing[func] = {k:Overloaded(list(v)) for k,v in args2ann.items()}
                                func.type = None    
            end = time.time()
            if end-start > 60*5:
                flag = 1
                break
        if flag == 1:
            mu_def = None
        elif len(solutions) == 0:
            mu_def = AnyType(0)
        else:
            mu_def = Overloaded(solutions)
        func.type = mu_def
        func.candidates = self.S3()
        print(func.name)
        print(func.type)        
        if self.defer_this_node:
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            for arg in func.arguments:
                self.tv_level[arg].clear()
            func.type = None
            return False
        def not_parametric(t):
            parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
            t = str(t)
            for p in parametric:
                if t.find(p) != -1:
                    return False
            return True
        def order_type(items):
            names = items[0].arg_names + ['']
            types = []
            for i, name in enumerate(names):
                types.append([])
                if i == len(names) -1:
                    for item in items:
                        if isinstance(item.ret_type, UnionType):
                            for t in item.ret_type.items:
                                if hasattr(t, 'type') and not_parametric(t):
                                    types[-1].append(t.type.fullname)
                                else:
                                    types[-1].append(str(t))
                        else:
                            if hasattr(item.ret_type, 'type') and not_parametric(item.ret_type):
                                types[-1].append(item.ret_type.type.fullname)
                            else:
                                types[-1].append(str(item.ret_type))
                else:
                    for item in items:
                        if hasattr(item.arg_types[i], 'type') and not_parametric(item.arg_types[i]):
                            types[-1].append(item.arg_types[i].type.fullname)
                        else:
                            types[-1].append(str(item.arg_types[i]))
            from difflib import SequenceMatcher
            new_types_all = []
            for i, name in enumerate(names):
                name = ''.join(name.split('_'))
                new_types = []
                long_length = 0
                long_lcs = '<no>'
                for typ in types[i]:
                    match = SequenceMatcher(None, name, typ).find_longest_match(0, len(name), 0, len(typ))
                    lcs = name[match.a: match.a + match.size] 
                    if len(lcs) > long_length:
                        long_length = len(lcs)
                        long_lcs = typ
                if long_length >= 4:
                    print(long_lcs)
                    new_types.append(long_lcs)
                    types[i].remove(long_lcs)
                primary = ['builtins.str', 'builtins.int', 'builtins.float', 'builtins.bytes', 'builtins.bool', 'builtins.object']
                third_party = ['numpy.ndarray', 'torch._tensor.Tensor', 'socket.socket']
                user_defined = self.user_defined
                parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
                for p in primary:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in third_party:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in user_defined:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in parametric:
                    for typ in types[i]:
                        if typ.find(p) != -1 and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                self.result_file2.write(str(new_types[:3])+'\n')
                new_types_all.append(new_types[:3])
            item_score = {}
            for item in items:
                score = 0
                for i, t in enumerate(item.arg_types):
                    if hasattr(t, 'type') and not_parametric(t):
                        identity = item.arg_types[i].type.fullname
                    else:
                        identity = str(t)
                    if identity in new_types_all[i]:
                        score += 1
                item_score[item] = score
            ordered_items = sorted(item_score.items(), key = lambda x:x[1], reverse=True)
            ordered_items = ordered_items[:3]
            annotation = '\n'.join(str(x[0]) for x in ordered_items)
            self.result_file.write(annotation+'\n\n')
        self.var_node = {k:v for k,v in original_var_node.items()}
        self.dp_dag = {k:v for k,v in original_dp_dag.items()}
        self.type_map = {k:v for k,v in original_type_map.items()}
        self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
        self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
        for arg in func.arguments:
            self.tv_level[arg].clear()
        self.record = {}
        self.result_file.write(func.name+' <func>\n')
        self.result_file2.write(func.name+'\n')
        if flag == 1:
            self.result_file.write('timeout\n')
        elif isinstance(func.type, AnyType):
            self.result_file.write('any\n')
        else:
            i = 0
            for t in (func.type.items):
                self.result_file.write(str(t)+'\n')
                i+=1
                if i>2:
                    break
        self.result_file.flush()
        self.result_file2.flush()
        return True
    def suggest_function_CPA2(self, node, from_class = False, force=False):
        def improve(a, t):
            if isinstance(t, TypeVarType):
                if 'T' in self.tv_level[a]:
                    return None
                else:
                    self.tv_level[a].append('T')
                    return set(self.S2(self.func_candidates[node], ground=a))
            else:
                if t.type.fullname in self.tv_level[a]:
                    return None
                else:  
                    self.tv_level[a].append(t.type.fullname)
                    return self.S3_for(t)
        def improvement():
            success = False
            for (a, t) in self.improvement:
                if a in nows:
                    now = set(nows[a])
                    ret = improve(a, t)
                    if ret is not None:
                        now.update(ret)
                        nows[a] = list(now)
                        success = True
            return success
        def try_to_update(updates):
            unsolvable = False
            hit = False
            for ground in updates:
                if ground in nows:
                    hit = True
                    now = nows[ground]
                    if now == self.S1(self.func_candidates[node], ground):
                        now = self.S2(self.func_candidates[node], ground)
                    elif now == self.S2(self.func_candidates[node], ground):
                        now = self.S3(self.func_candidates[node], ground)
                    else:
                        unsolvable = True
                    nows[ground] = now
                elif hasattr(self, "class_vars") and ground in self.class_vars:
                    hit = True
                    if ground not in self.none_global:
                        self.type_map[ground] = self.makeS4Type(self.type_map[ground])
                    else:
                        if self.type_map[ground].items == self.S1():
                            self.type_map[ground] = self.makeS2Type()
                        elif self.type_map[ground].items == self.S2():
                            self.type_map[ground] = self.makeS3Type()
                        elif self.type_map[ground].items == self.S3():
                            self.type_map[ground] = self.makeS4Type()
                        else:
                            unsolvable = True
            return not(not hit or unsolvable)
        def add_attr(x, attrs):
            candidates = self.s2 + self.s3
            for candidate in candidates:
                candidate_info = candidate.type
                retrieve_attr_res = [candidate_info.get(x) for x in attrs]
                if all([x is not None for x in retrieve_attr_res]):
                    if candidate not in x:
                        list_user_type = self.type_checker().named_type_with_type_var('builtins.list', candidate)
                        set_user_type = self.type_checker().named_type_with_type_var('builtins.set', candidate)
                        x.append(candidate)
                        x.append(list_user_type)
                        x.append(set_user_type)
            return x
        def add_type(x, types):
            for typ in types:
                if typ not in x:
                    x.append(x)
            return x
        if node.unanalyzed_type is not None:
            return
        node.type = None
        func_name = node.fullname
        line_no = node.line
        is_method = bool(node.info) and not node.is_static
        base = self.get_starting_type(node)
        if node not in self.func_class:
            if bool(node.info):
                self.func_class[node] = node.info
            else:
                self.func_class[node] = None
        nows = {}
        self.record = {}
        for arg in node.arguments:
            nows[arg] = self.S3(node, arg)
            self.arg_level[arg] = 1
        original_var_node = {k:v for k,v in self.var_node.items()}
        original_type_map = {k:v for k, v in self.type_map.items()}
        original_wide_type_map = {k:v for k, v in self.wide_type_map.items()}
        original_infer_map = {k:v for k,v in self.expr_checker.local_infer_map.items()}
        original_dp_dag = {k:v for k,v in self.dp_dag.items()}
        list_now = []
        for i in range(len(base.arg_kinds)):
            argument = node.arguments[i]
            list_now.append(nows[argument])
        combinations = itertools.product(*list_now)
        solutions = []
        start = time.time()
        flag = 0
        for combination in combinations:
            annots = []
            for i in range(len(base.arg_kinds)):
                argument = node.arguments[i]
                typ = combination[i]
                if i == 0 and is_method:
                    annots.append(Instance(node.info, [AnyType(TypeOfAny.from_omitted_generics)] * len(node.info.defn.type_vars)))
                else:
                    annots.append(typ)
            node.type = base.copy_modified(arg_types=annots)
            func = node
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.cache_type_map.clear()
            self.defer_this_node = False        
            self.infer_dependency_map = {}
            self.single_incompatible.clear()
            self.incompatible.clear()
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.added_attr.clear()
            self.message.clear()
            self.improvement.clear()
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            grounds = []
            self.expr_checker.timeout = False
            self.visit_func_def(node)
            if self.defer_this_node:
                break
            else:
                worklist, updates = self.global_solving()
                if len(worklist) > 0:
                    new_worklist = []
                    none_type = NoneType()
                    ret_node = TempNode(none_type)
                    for w in worklist:
                        phi_ret = []
                        if len(self.infer_dependency_map) == 0:
                            pass
                        elif len(self.infer_dependency_map) == 1 and all([len(x) == 0 for x in self.infer_dependency_map.values()]):
                            for node_, typ in self.infer_dependency_map:
                                phi_ret.append(typ)
                        else:
                            for node_, typ in self.infer_dependency_map:
                                if len(self.infer_dependency_map[(node_, typ)]) == 0:
                                    phi_ret.append(typ)
                                else:
                                    for possiblity in self.infer_dependency_map[(node_, typ)]:
                                        if self.contains_all(possiblity, w):
                                            phi_ret.append(typ)
                                            break
                                        else:
                                            pass
                        if len(phi_ret) > 1:
                            phi_ret = UnionType.make_union(phi_ret)
                        elif len(phi_ret) == 1:
                            phi_ret = phi_ret[0]
                        else:
                            if len(self.infer_dependency_map) == 0:
                                phi_ret = NoneType(0)
                            else:
                                phi_ret = UnionType.make_union([x[1] for x in self.infer_dependency_map.keys()])
                        if not isinstance(phi_ret, NoneType):
                            try:
                                w.append((node_, phi_ret))
                                new_worklist.append(w)
                            except Exception:
                                pass
                        else:
                            w.append((ret_node, none_type))
                            new_worklist.append(w)
                        self.infer_dependency_map.clear()
                        worklist = new_worklist
                        args = [x for x in func.arguments]
                        if not from_class:
                            for w in worklist:
                                ann = self.to_annotation(base, w, args)
                                if ann not in solutions:
                                    solutions.append(ann)
                        else:
                            self.func_solutions[func] = worklist
                            reduce, args2ann = self.try_reduce(base, worklist, args)
                            reduce = True
                            if reduce:
                                if len(args2ann) == 0:
                                    func.type = base
                                else:
                                    ftype = Overloaded(list(list(args2ann.values())[0]))
                                    solutions.extend(list(list(args2ann.values())[0]))
                                    func.type = ftype
                            else:
                                self.method_typing[func] = {k:Overloaded(list(v)) for k,v in args2ann.items()}
                                func.type = None    
            end = time.time()
            if end-start > 60*5:
                flag = 1
                break
        if flag == 1:
            mu_def = None
        elif len(solutions) == 0:
            mu_def = AnyType(0)
        else:
            mu_def = Overloaded(solutions)
        func.type = mu_def
        func.candidates = self.S3()
        print(func.name)
        print(func.type)        
        if self.defer_this_node:
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            for arg in func.arguments:
                self.tv_level[arg].clear()
            func.type = None
            return False
        def not_parametric(t):
            parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
            t = str(t)
            for p in parametric:
                if t.find(p) != -1:
                    return False
            return True
        def order_type(items):
            names = items[0].arg_names + ['']
            types = []
            for i, name in enumerate(names):
                types.append([])
                if i == len(names) -1:
                    for item in items:
                        if isinstance(item.ret_type, UnionType):
                            for t in item.ret_type.items:
                                if hasattr(t, 'type') and not_parametric(t):
                                    types[-1].append(t.type.fullname)
                                else:
                                    types[-1].append(str(t))
                        else:
                            if hasattr(item.ret_type, 'type') and not_parametric(item.ret_type):
                                types[-1].append(item.ret_type.type.fullname)
                            else:
                                types[-1].append(str(item.ret_type))
                else:
                    for item in items:
                        if hasattr(item.arg_types[i], 'type') and not_parametric(item.arg_types[i]):
                            types[-1].append(item.arg_types[i].type.fullname)
                        else:
                            types[-1].append(str(item.arg_types[i]))
            from difflib import SequenceMatcher
            new_types_all = []
            for i, name in enumerate(names):
                name = ''.join(name.split('_'))
                new_types = []
                long_length = 0
                long_lcs = '<no>'
                for typ in types[i]:
                    match = SequenceMatcher(None, name, typ).find_longest_match(0, len(name), 0, len(typ))
                    lcs = name[match.a: match.a + match.size] 
                    if len(lcs) > long_length:
                        long_length = len(lcs)
                        long_lcs = typ
                if long_length >= 4:
                    print(long_lcs)
                    new_types.append(long_lcs)
                    types[i].remove(long_lcs)
                primary = ['builtins.str', 'builtins.int', 'builtins.float', 'builtins.bytes', 'builtins.bool', 'builtins.object']
                third_party = ['numpy.ndarray', 'torch._tensor.Tensor', 'socket.socket']
                user_defined = self.user_defined
                parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
                for p in primary:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in third_party:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in user_defined:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                for p in parametric:
                    for typ in types[i]:
                        if typ.find(p) != -1 and typ not in new_types:
                            new_types.append(typ)
                print(new_types)
                self.result_file2.write(str(new_types[:3])+'\n')
                new_types_all.append(new_types[:3])
            item_score = {}
            for item in items:
                score = 0
                for i, t in enumerate(item.arg_types):
                    if hasattr(t, 'type') and not_parametric(t):
                        identity = item.arg_types[i].type.fullname
                    else:
                        identity = str(t)
                    if identity in new_types_all[i]:
                        score += 1
                item_score[item] = score
            ordered_items = sorted(item_score.items(), key = lambda x:x[1], reverse=True)
            ordered_items = ordered_items[:3]
            annotation = '\n'.join(str(x[0]) for x in ordered_items)
            self.result_file.write(annotation+'\n\n')
        self.var_node = {k:v for k,v in original_var_node.items()}
        self.dp_dag = {k:v for k,v in original_dp_dag.items()}
        self.type_map = {k:v for k,v in original_type_map.items()}
        self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
        self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
        for arg in func.arguments:
            self.tv_level[arg].clear()
        self.record = {}
        self.result_file.write(func.name+' <func>\n')
        self.result_file2.write(func.name+'\n')
        if flag == 1:
            self.result_file.write('timeout\n')
        elif isinstance(func.type, AnyType):
            self.result_file.write('any\n')
        else:
            i = 0
            for t in (func.type.items):
                self.result_file.write(str(t)+'\n')
                i+=1
                if i>2:
                    break
        self.result_file.flush()
        self.result_file2.flush()
        return True
    def put_into_correct_level(self, func, argument, at):
        if self.mode == 'CPA':
            self.func_finished[func][argument].add(at)
        if isinstance(at, Instance):
            self.func_candidates[func][argument].add(at)
            self.func_must[func][argument].add(at)
            t = (at.type, at.args)
            if at.type.fullname == 'builtins.list' or at.type.fullname == 'builtins.set' or at.type.fullname == 'builtins.dict':
                self.func_s3[func][argument].add(at)
            else:
                self.func_s2[func][argument].add(at)
        elif isinstance(at, CallableType):
            self.func_candidates[func][argument].add(at)
            self.func_must[func][argument].add(at)
            self.func_s3[func][argument].add(at)
        elif not isinstance(at, AnyType) and not isinstance(at, NoneType) and not isinstance(at, PartialType) and not isinstance(at, UnionType) and not isinstance(at, TypeVarType) and not isinstance(at, CallableType) and not isinstance(at, UninhabitedType):
            self.func_candidates[func][argument].add(at)
            self.func_must[func][argument].add(at)
            self.func_s3[func][argument].add(at)
    def init_type_seeds(self, node):
        self.func_candidates[node] = {}
        for arg in node.arguments:
            self.func_s1[node][arg] = set(copy(self.s1))
            self.func_s2[node][arg] = set(copy(self.s2))
            self.func_s3[node][arg] = set(copy(self.s3))
            self.func_candidates[node][arg] = set(self.S3(node, arg))
            self.func_must[node][arg] = set()
            self.func_finished[node][arg] = set()
            if arg.initializer is not None:
                default_types = self.expr_checker.accept(arg.initializer)
                for dt in default_types:
                    self.put_into_correct_level(node, arg, dt)
    def suggest_function(self, node, from_class = False, force=False, init=False):
        def get_candidates(x):
            if isinstance(x, (set, list)):
                return len(x)
            else:
                return 1
        def improve(a):
            if len(nows[a]) == len(self.S1(node, a)): 
                return self.S2(node, a)
            elif len(nows[a]) == len(self.S2(node, a)): 
                return self.S3(node, a)
            else:
                return None
        def improvement():
            success = False
            args = set()
            for (a, t) in self.improvement:
                args.add(a)
            for a in args:
                if a in nows and a is not self.self_arg:
                    now = set(nows[a])
                    ret = improve(a)
                    if ret is not None:
                        now.update(ret)
                        nows[a] = now
                        success = True
            return success
        def check_must():
            for arg in nows:
                if not self.func_must[node][arg].issubset(nows[arg]):
                    self.expr_checker.add_improvement(arg)
                    return False
            return True
        def try_to_update(updates):
            unsolvable = False
            hit = False
            for ground in updates:
                if ground in nows:
                    hit = True
                    now = nows[ground]
                    if now == self.S1(self.func_candidates[node], ground):
                        now = self.S2(self.func_candidates[node], ground)
                    elif now == self.S2(self.func_candidates[node], ground):
                        now = self.S3(self.func_candidates[node], ground)
                    else:
                        unsolvable = True
                    nows[ground] = now
                elif hasattr(self, "class_vars") and ground in self.class_vars:
                    hit = True
                    if ground not in self.none_global:
                        self.type_map[ground] = self.makeS4Type(self.type_map[ground])
                    else:
                        if self.type_map[ground].items == self.S1():
                            self.type_map[ground] = self.makeS2Type()
                        elif self.type_map[ground].items == self.S2():
                            self.type_map[ground] = self.makeS3Type()
                        elif self.type_map[ground].items == self.S3():
                            self.type_map[ground] = self.makeS4Type()
                        else:
                            unsolvable = True
            return not(not hit or unsolvable)
        def isS1(x):
            if isinstance(x, Instance):
                if x.type.name == 'object':
                    return True
            elif isinstance(x, MaybeTypes):
                if len(x.items) == 1:
                    t = x.items[0].type
                    if t.name == 'object':
                        return True
            return False
        def add_attr(x, attrs):
            candidates = self.s2 + self.s3
            for candidate in candidates:
                candidate_info = candidate.type
                retrieve_attr_res = [candidate_info.get(x) for x in attrs]
                if all([x is not None for x in retrieve_attr_res]):
                    if candidate not in x:
                        list_user_type = self.type_checker().named_type_with_type_var('builtins.list', candidate)
                        set_user_type = self.type_checker().named_type_with_type_var('builtins.set', candidate)
                        x.append(candidate)
                        x.append(list_user_type)
                        x.append(set_user_type)
            return x
        def add_type(x, types):
            for typ in types:
                if typ not in x:
                    x.append(x)
            return x

        def PCT(l, r):
            nonlocal worklist
            if l + 1 != r:
                mid = int((l + r) / 2)

                PCT(l, mid)
                PCT(mid, r)
            now_grounds = grounds[l:r]
            for g in now_grounds:
                new_worklist = []
                types = self.wide_type_map[g]
                for typ in types:
                    id_pair = (g, typ)
                    if not (g in single_incompatible1 and typ in single_incompatible1[g]):
                        for state in worklist:
                            if (id_pair not in double_incompatible) or (not any([self.contains_all(x, state) for x in double_incompatible[id_pair]])):
                                new_state = [x for x in state]
                                new_state.append(id_pair)
                                new_worklist.append(new_state)  
                            else:
                                pass
                    else:
                        pass
                if len(new_worklist) > 0:
                    worklist = new_worklist
            if len(worklist) > self.combination_limits:
                worklist = []
        if node.unanalyzed_type is not None:
            return
        if node not in self.func_candidates:
            self.init_type_seeds(node)
        if node not in self.func_class:
            if bool(node.info):
                self.func_class[node] = node.info
            else:
                self.func_class[node] = None
        is_method = bool(node.info) and not node.is_static
        if node.fullname not in self.func_name_order:
            if node.fullname.find('__init__') == -1:
                with open(f'results/funcs_ret-{self.manager.options.tag}', 'a+') as f:
                    f.write(str(len(self.func_name_order))+',')
                self.func_name_order.append(node.fullname)
                for i, a in enumerate(node.arguments):
                    if is_method and i == 0:
                        continue
                    self.func_name_order.append('\n')
                with open(f'results/funcs-{self.manager.options.tag}', 'a+') as f:
                    f.write(node.fullname+'\n')
                    for i, a in enumerate(node.arguments):
                        if is_method and i == 0:
                            continue
                        f.write('\n')
        if init:
            return
        node.type = None
        func_name = node.fullname
        print(func_name)
        line_no = node.line
        base = self.get_starting_type(node)
        nows = {}
        self.record = {}
        self.self_arg = None
        for arg in node.arguments:
            if self.mode == 'PTI':
                nows[arg] = self.S1(node, arg) 
            else:
                nows[arg] = self.S2(node, arg)
            self.arg_level[arg] = 1
        original_var_node = {k:v for k,v in self.var_node.items()}
        original_type_map = {k:v for k, v in self.type_map.items()}
        original_wide_type_map = {k:v for k, v in self.wide_type_map.items()}
        original_infer_map = {k:v for k,v in self.expr_checker.local_infer_map.items()}
        original_dp_dag = {k:v for k,v in self.dp_dag.items()}
        while True:
            all_annots = []
            for arg in nows:
                all_annots.append(nows[arg])
            annots = []
            for i in range(len(base.arg_kinds)):
                argument = node.arguments[i]
                all_annots[i] = nows[argument]
                if argument.initializer is not None:
                    all_annots[i] = nows[argument]
                if i == 0 and is_method:
                    self.self_arg = argument
                    annots.append(Instance(node.info, [AnyType(TypeOfAny.from_omitted_generics)] * len(node.info.defn.type_vars)))
                else:
                    annots.append(all_annots[i])
            node.type = base.copy_modified(arg_types=annots)
            func = node
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.cache_type_map.clear()
            self.defer_this_node = False        
            self.infer_dependency_map = {}
            self.single_incompatible.clear()
            self.incompatible.clear()
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.added_attr.clear()
            self.message.clear()
            self.improvement.clear()
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            grounds = []
            start = time.time()
            self.expr_checker.timeout = False
            self.current_node = node
            self.visit_func_def(node)
            if self.defer_this_node:
                break
            else:
                worklist, updates = self.global_solving()
                musted = check_must()
                if len(worklist) > 0 and musted:
                    break
                else:
                    if self.mode == 'PTI':
                        success = improvement()
                        if not success:
                            break
                    else:
                        break
        if self.defer_this_node:
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            for arg in func.arguments:
                self.tv_level[arg].clear()
            func.type = None
            return False
        self.func_finished[node] = nows
        if self.expr_checker.timeout:
            self.expr_checker.timeout = False
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            self.record = {}
            func.type = base
            return True
        for var in self.wide_type_map:
            flag = 0
            for var2, typ in self.expr_checker.local_infer_map:
                if var2 == var:
                    source_pairss = self.expr_checker.local_infer_map[(var2, typ)]
                    source_nodes = []
                    for source_pairs in source_pairss:
                        source_nodes.extend([x[0] for x in source_pairs])
                    if not all(isinstance(x, FlowNode) for x in source_nodes):
                        flag = 1
                        break
            if flag == 0 and var not in grounds:
                grounds.append(var)



        if not USE_PCT:

            grounds = sorted(grounds, key=lambda x:get_candidates(self.wide_type_map[x]))
        single_incompatible1 = self.single_incompatible
        double_incompatible = self.incompatible
        worklist = [['start']]


        # grounds = [x for x in grounds if isinstance(x, Argument)]
        # single_incompatible1 = {k:v for k, v in single_incompatible1.items() if isinstance(k, Argument)}

        


        for g in grounds:
            if USE_PCT and isinstance(g, Argument):
                continue
            new_worklist = []
            types = self.wide_type_map[g]
            for typ in types:
                id_pair = (g, typ)
                if not (g in single_incompatible1 and typ in single_incompatible1[g]):
                    for state in worklist:
                        if (id_pair not in double_incompatible) or (not any([self.contains_all(x, state) for x in double_incompatible[id_pair]])):
                            new_state = [x for x in state]
                            new_state.append(id_pair)
                            new_worklist.append(new_state)  
                        else:
                            pass
                else:
                    pass
            if len(new_worklist) > 0:
                worklist = new_worklist
        if USE_PCT:
            grounds = [x for x in grounds if isinstance(x, Argument)]
            if len(grounds) > 0:
                PCT(0, len(grounds))


        if len(worklist) > self.combination_limits:
            worklist = []
        new_worklist = []
        none_type = NoneType()
        ret_node = TempNode(none_type)
        for w in worklist:
            phi_ret = []
            if len(self.infer_dependency_map) == 0:
                pass
            elif len(self.infer_dependency_map) == 1 and all([len(x) == 0 for x in self.infer_dependency_map.values()]):
                for node, typ in self.infer_dependency_map:
                    phi_ret.append(typ)
            else:
                for node, typ in self.infer_dependency_map:
                    if len(self.infer_dependency_map[(node, typ)]) == 0:
                        phi_ret.append(typ)
                    else:
                        for possiblity in self.infer_dependency_map[(node, typ)]:
                            if self.contains_all(possiblity, w):
                                phi_ret.append(typ)
                                break
                            else:
                                pass
            if len(phi_ret) > 1:
                phi_ret = [x for x in phi_ret if not isinstance(x, NoneType)]
                phi_ret = make_simplified_union(phi_ret)
            elif len(phi_ret) == 1:
                phi_ret = phi_ret[0]
            else:
                if len(self.infer_dependency_map) == 0:
                    phi_ret = NoneType(0)
                else:
                    phi_ret = make_simplified_union([x[1] for x in self.infer_dependency_map.keys()])
            if phi_ret is not None:
                w.append((node, phi_ret))
                new_worklist.append(w)
            else:
                w.append((ret_node, none_type))
                new_worklist.append(w)
        self.infer_dependency_map.clear()
        worklist = new_worklist
        solutions = []  
        args = [x for x in func.arguments]
        if not from_class:
            for w in worklist:
                ann = self.to_annotation(base, w, args)
                if ann not in solutions:
                    solutions.append(ann)
            if len(solutions) == 0:
                solutions.append(base)
            solutions = sorted(solutions, key=lambda x: str(x))
            mu_def = Overloaded(solutions)
            func.type = mu_def
            print(func.name)
            print(func.type)
        else:
            self.func_solutions[func] = worklist
            reduce, args2ann = self.try_reduce(base, worklist, args)
            reduce = True
            if reduce:
                if len(args2ann) == 0:
                    func.type = base
                else:
                    ftype = Overloaded(list(list(args2ann.values())[0]))
                    func.type = ftype
            else:
                self.method_typing[func] = {k:Overloaded(list(v)) for k,v in args2ann.items()}
                func.type = None
            print(func.name)
            print(func.type)
        def not_parametric(t):
            parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
            t = str(t)
            for p in parametric:
                if t.find(p) != -1:
                    return False
            return True
        def identity(t):
            if hasattr(t, 'type') and not_parametric(t):
                if t.type == None:
                    idt = 'None'
                else:
                    idt = t.type.fullname
            else:
                idt = str(t)
            return idt
        def order_type(items):
            names = items[0].arg_names + ['']
            types = []
            for i, name in enumerate(names):
                types.append([])
                if i == len(names) -1:
                    for item in items:
                        if isinstance(item.ret_type, UnionType):
                            for t in item.ret_type.items:
                                if hasattr(t, 'type') and not_parametric(t):
                                    if t.type == None:
                                        types[-1].append('None')
                                    else:
                                        types[-1].append(t.type.fullname)
                                else:
                                    types[-1].append(str(t))
                        else:
                            if hasattr(item.ret_type, 'type') and not_parametric(item.ret_type):
                                if item.ret_type.type == None:
                                    types[-1].append('None')
                                else:
                                    types[-1].append(item.ret_type.type.fullname)
                            else:
                                types[-1].append(str(item.ret_type))
                else:
                    for item in items:
                        if hasattr(item.arg_types[i], 'type') and not_parametric(item.arg_types[i]):
                            types[-1].append(item.arg_types[i].type.fullname)
                        else:
                            types[-1].append(str(item.arg_types[i]))
            from difflib import SequenceMatcher
            new_types_all = []
            for i, name in enumerate(names):
                name = str(name)
                name = ''.join(name.split('_'))
                new_types = []
                long_length = 0
                long_lcs = '<no>'
                for typ in types[i]:
                    match = SequenceMatcher(None, name, typ).find_longest_match(0, len(name), 0, len(typ))
                    lcs = name[match.a: match.a + match.size] 
                    if len(lcs) > long_length:
                        long_length = len(lcs)
                        long_lcs = typ
                if long_length >= 4:
                    print(long_lcs)
                    new_types.append(long_lcs)
                    types[i].remove(long_lcs)
                primary = ['builtins.object', 'builtins.str', 'builtins.int', 'builtins.float', 'builtins.bytes', 'builtins.bool']
                third_party = ['numpy.ndarray', 'torch._tensor.Tensor', 'socket.socket']
                user_defined = self.user_defined
                parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
                for p in primary:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in third_party:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in user_defined:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in parametric:
                    for typ in types[i]:
                        if typ.find(p) != -1 and typ not in new_types:
                            new_types.append(typ)
                for typ in types[i]:
                    if typ not in new_types:
                        new_types.append(typ)
                to_print = new_types[:3]
                if 'builtins.int' in new_types and 'builtins.bool' in new_types:
                    new_types.remove('builtins.bool')
                if 'builtins.list[builtins.int]' in new_types and 'builtins.list[builtins.bool]' in new_types:
                    new_types.remove('builtins.list[builtins.bool]')
                if 'builtins.list[builtins.int]' in new_types and 'builtins.bytes' in new_types:
                    new_types.remove('builtins.bytes')
                self.result_file2.write(str(new_types[:3])+'\n')
                new_types_all.append(new_types)
            def strize(x):
                if isinstance(x, UnionType):
                    return '/'.join([str(y) for y in x.items])
                return str(x)
            def rank(l, x):
                if x in l:
                    return l.index(x)
                else:
                    return 1000000
            def topize(l):
                ret = []
                for x in l:
                    if x not in ret:
                        ret.append(x)
                    if len(ret) == 3:
                        return ret
                return ret
            strs = []
            rets = []
            origin_rets = [x.ret_type for x in items]
            topn = sorted(origin_rets, key = lambda x:rank(new_types_all[-1], identity(x)))
            top3 = topize(topn)
            rets = [strize(x) for x in top3]
            ret_str = '/'.join(rets)
            strs.append(ret_str)
            for i, a in enumerate(func.arguments):
                if is_method and i == 0 :
                    continue
                origin_args = [x.arg_types[i] for x in items]
                topn = sorted(origin_args, key = lambda x:rank(new_types_all[i], identity(x)))
                top3 = topize(topn)
                args = [strize(x) for x in top3]
                arg_str = '/'.join(args)
                strs.append(arg_str)
            self.func_name_recorder[func.fullname] = strs
            return
            self.result_file.write(annotation+'\n\n')
        self.var_node = {k:v for k,v in original_var_node.items()}
        self.dp_dag = {k:v for k,v in original_dp_dag.items()}
        self.type_map = {k:v for k,v in original_type_map.items()}
        self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
        self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
        for arg in func.arguments:
            self.tv_level[arg].clear()
        self.record = {}
        self.result_file.write(func.name+'\n')
        self.result_file2.write(func.name+'\n')
        sorted_items = sorted(func.type.items, key=lambda x:str(x))
        for t in (sorted_items):
            self.result_file.write(str(t)+'\n')
        order_type(func.type.items)
        self.result_file.flush()
        self.result_file2.flush()
        return True
    def suggest_function_CPA(self, node, from_class = False, force=False, init=False):
        def get_candidates(x):
            if isinstance(x, (set, list)):
                return len(x)
            else:
                return 1
        def improve(a):
            if len(nows[a]) == len(self.S1(node, a)): 
                return self.S2(node, a)
            elif len(nows[a]) == len(self.S2(node, a)): 
                return self.S3(node, a)
            else:
                return None
        def improvement():
            success = False
            args = set()
            for (a, t) in self.improvement:
                args.add(a)
            for a in args:
                if a in nows and a is not self.self_arg:
                    now = set(nows[a])
                    ret = improve(a)
                    if ret is not None:
                        now.update(ret)
                        nows[a] = now
                        success = True
            return success
        def check_must():
            for arg in nows:
                if not self.func_must[node][arg].issubset(nows[arg]):
                    self.expr_checker.add_improvement(arg)
                    return False
            return True
        def try_to_update(updates):
            unsolvable = False
            hit = False
            for ground in updates:
                if ground in nows:
                    hit = True
                    now = nows[ground]
                    if now == self.S1(self.func_candidates[node], ground):
                        now = self.S2(self.func_candidates[node], ground)
                    elif now == self.S2(self.func_candidates[node], ground):
                        now = self.S3(self.func_candidates[node], ground)
                    else:
                        unsolvable = True
                    nows[ground] = now
                elif hasattr(self, "class_vars") and ground in self.class_vars:
                    hit = True
                    if ground not in self.none_global:
                        self.type_map[ground] = self.makeS4Type(self.type_map[ground])
                    else:
                        if self.type_map[ground].items == self.S1():
                            self.type_map[ground] = self.makeS2Type()
                        elif self.type_map[ground].items == self.S2():
                            self.type_map[ground] = self.makeS3Type()
                        elif self.type_map[ground].items == self.S3():
                            self.type_map[ground] = self.makeS4Type()
                        else:
                            unsolvable = True
            return not(not hit or unsolvable)
        def isS1(x):
            if isinstance(x, Instance):
                if x.type.name == 'object':
                    return True
            elif isinstance(x, MaybeTypes):
                if len(x.items) == 1:
                    t = x.items[0].type
                    if t.name == 'object':
                        return True
            return False
        def add_attr(x, attrs):
            candidates = self.s2 + self.s3
            for candidate in candidates:
                candidate_info = candidate.type
                retrieve_attr_res = [candidate_info.get(x) for x in attrs]
                if all([x is not None for x in retrieve_attr_res]):
                    if candidate not in x:
                        list_user_type = self.type_checker().named_type_with_type_var('builtins.list', candidate)
                        set_user_type = self.type_checker().named_type_with_type_var('builtins.set', candidate)
                        x.append(candidate)
                        x.append(list_user_type)
                        x.append(set_user_type)
            return x
        def add_type(x, types):
            for typ in types:
                if typ not in x:
                    x.append(x)
            return x
        if node.unanalyzed_type is not None:
            return
        if node.fullname.find('__init__') != -1:
            return
        if node not in self.func_candidates:
            self.init_type_seeds(node)
        if node not in self.func_class:
            if bool(node.info):
                self.func_class[node] = node.info
            else:
                self.func_class[node] = None
        if init:
            return
        is_method = bool(node.info) and not node.is_static
        if node.fullname in self.func_name_order and node.type == None:
            self.result_file.write(node.fullname + ' ; ' + 'None' +'\n')
            self.result_file.flush()
            return
        else:
            pass
            if node.fullname.find('__init__') != -1:
                return
        node.type = None
        func_name = node.fullname
        print(func_name)
        line_no = node.line
        base = self.get_starting_type(node)
        nows = {}
        self.record = {}
        self.self_arg = None
        for arg in node.arguments:
            if self.mode == 'PTI':
                nows[arg] = self.S1(node, arg) 
            else:
                nows[arg] = self.S3(node, arg)
            self.arg_level[arg] = 1
        original_var_node = {k:v for k,v in self.var_node.items()}
        original_type_map = {k:v for k, v in self.type_map.items()}
        original_wide_type_map = {k:v for k, v in self.wide_type_map.items()}
        original_infer_map = {k:v for k,v in self.expr_checker.local_infer_map.items()}
        original_dp_dag = {k:v for k,v in self.dp_dag.items()}
        list_now = []
        for i in range(len(base.arg_kinds)):
            argument = node.arguments[i]
            list_now.append(nows[argument])
        combinations = itertools.product(*list_now)
        solutions = []
        start = time.time()
        flag = 0
        for combination in combinations:
            annots = []
            for i in range(len(base.arg_kinds)):
                argument = node.arguments[i]
                typ = combination[i]
                typ = {typ}
                if i == 0 and is_method:
                    annots.append(Instance(node.info, [AnyType(TypeOfAny.from_omitted_generics)] * len(node.info.defn.type_vars)))
                else:
                    annots.append(typ)
            node.type = base.copy_modified(arg_types=annots)
            func = node
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.cache_type_map.clear()
            self.defer_this_node = False        
            self.infer_dependency_map = {}
            self.single_incompatible.clear()
            self.incompatible.clear()
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.added_attr.clear()
            self.message.clear()
            self.improvement.clear()
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            grounds = []
            self.expr_checker.timeout = False
            self.visit_func_def(node)
            if self.defer_this_node:
                break
            else:
                worklist, updates = self.global_solving()
                musted = check_must()
                if len(worklist) > 0:
                    new_worklist = []
                    none_type = NoneType()
                    ret_node = TempNode(none_type)
                    for w in worklist:
                        phi_ret = []
                        if len(self.infer_dependency_map) == 0:
                            pass
                        elif len(self.infer_dependency_map) == 1 and all([len(x) == 0 for x in self.infer_dependency_map.values()]):
                            for node_, typ in self.infer_dependency_map:
                                phi_ret.append(typ)
                        else:
                            for node_, typ in self.infer_dependency_map:
                                if len(self.infer_dependency_map[(node_, typ)]) == 0:
                                    phi_ret.append(typ)
                                else:
                                    for possiblity in self.infer_dependency_map[(node_, typ)]:
                                        if self.contains_all(possiblity, w):
                                            phi_ret.append(typ)
                                            break
                                        else:
                                            pass
                        if len(phi_ret) > 1:
                            phi_ret = UnionType.make_union(phi_ret)
                        elif len(phi_ret) == 1:
                            phi_ret = phi_ret[0]
                        else:
                            if len(self.infer_dependency_map) == 0:
                                phi_ret = NoneType(0)
                            else:
                                phi_ret = UnionType.make_union([x[1] for x in self.infer_dependency_map.keys()])
                        if not isinstance(phi_ret, NoneType):
                            try:
                                w.append((node_, phi_ret))
                                new_worklist.append(w)
                            except Exception:
                                pass
                        else:
                            w.append((ret_node, none_type))
                            new_worklist.append(w)
                        self.infer_dependency_map.clear()
                        worklist = new_worklist
                        args = [x for x in func.arguments]
                        if not from_class:
                            for w in worklist:
                                ann = self.to_annotation(base, w, args)
                                if ann not in solutions:
                                    solutions.append(ann)
                        else:
                            self.func_solutions[func] = worklist
                            reduce, args2ann = self.try_reduce(base, worklist, args)
                            reduce = True
                            if reduce:
                                if len(args2ann) == 0:
                                    func.type = base
                                else:
                                    ftype = Overloaded(list(list(args2ann.values())[0]))
                                    solutions.extend(list(list(args2ann.values())[0]))
                                    func.type = ftype
                            else:
                                self.method_typing[func] = {k:Overloaded(list(v)) for k,v in args2ann.items()}
                                func.type = None    
            end = time.time()
            if end-start > 5*60:
                flag = 1
                break
        if self.defer_this_node:
            self.var_node = {k:v for k,v in original_var_node.items()}
            self.type_map = {k:v for k,v in original_type_map.items()}
            self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
            self.dp_dag = {k:v for k,v in original_dp_dag.items()}
            self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
            for arg in func.arguments:
                self.tv_level[arg].clear()
            func.type = None
            return False
        if flag == 1:
            mu_def = None
            self.result_file.write(node.fullname + ' ; ' + 'None' +'\n')
            self.result_file.flush()
        elif len(solutions) == 0:
            mu_def = base
        else:
            mu_def = Overloaded(solutions)
        func.type = mu_def
        self.func_name_order.append(node.fullname)
        print(func.name)
        print(func.type)    
        self.func_name_order.append(node.fullname)
        def not_parametric(t):
            parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
            t = str(t)
            for p in parametric:
                if t.find(p) != -1:
                    return False
            return True
        def identity(t):
            if hasattr(t, 'type') and not_parametric(t):
                if t.type == None:
                    idt = 'None'
                else:
                    idt = t.type.fullname
            else:
                idt = str(t)
            return idt
        def order_type(items):
            names = items[0].arg_names + ['']
            types = []
            for i, name in enumerate(names):
                types.append([])
                if i == len(names) -1:
                    for item in items:
                        if isinstance(item.ret_type, UnionType):
                            for t in item.ret_type.items:
                                if hasattr(t, 'type') and not_parametric(t):
                                    if t.type == None:
                                        types[-1].append('None')
                                    else:
                                        types[-1].append(t.type.fullname)
                                else:
                                    types[-1].append(str(t))
                        else:
                            if hasattr(item.ret_type, 'type') and not_parametric(item.ret_type):
                                if item.ret_type.type == None:
                                    types[-1].append('None')
                                else:
                                    types[-1].append(item.ret_type.type.fullname)
                            else:
                                types[-1].append(str(item.ret_type))
                else:
                    for item in items:
                        if hasattr(item.arg_types[i], 'type') and not_parametric(item.arg_types[i]):
                            types[-1].append(item.arg_types[i].type.fullname)
                        else:
                            types[-1].append(str(item.arg_types[i]))
            from difflib import SequenceMatcher
            new_types_all = []
            for i, name in enumerate(names):
                name = str(name)
                name = ''.join(name.split('_'))
                new_types = []
                long_length = 0
                long_lcs = '<no>'
                for typ in types[i]:
                    match = SequenceMatcher(None, name, typ).find_longest_match(0, len(name), 0, len(typ))
                    lcs = name[match.a: match.a + match.size] 
                    if len(lcs) > long_length:
                        long_length = len(lcs)
                        long_lcs = typ
                if long_length >= 4:
                    print(long_lcs)
                    new_types.append(long_lcs)
                    types[i].remove(long_lcs)
                primary = ['builtins.object', 'builtins.str', 'builtins.int', 'builtins.float', 'builtins.bytes', 'builtins.bool']
                third_party = ['numpy.ndarray', 'torch._tensor.Tensor', 'socket.socket']
                user_defined = self.user_defined
                parametric = ['builtins.list', 'builtins.set', 'builtins.dict', 'builtins.tuple', 'Tuple']
                for p in primary:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in third_party:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in user_defined:
                    for typ in types[i]:
                        if typ == p and typ not in new_types:
                            new_types.append(typ)
                for p in parametric:
                    for typ in types[i]:
                        if typ.find(p) != -1 and typ not in new_types:
                            new_types.append(typ)
                for typ in types[i]:
                    if typ not in new_types:
                        new_types.append(typ)
                to_print = new_types[:3]
                if 'builtins.int' in new_types and 'builtins.bool' in new_types:
                    new_types.remove('builtins.bool')
                if 'builtins.list[builtins.int]' in new_types and 'builtins.list[builtins.bool]' in new_types:
                    new_types.remove('builtins.list[builtins.bool]')
                if 'builtins.list[builtins.int]' in new_types and 'builtins.bytes' in new_types:
                    new_types.remove('builtins.bytes')
                self.result_file2.write(str(new_types[:3])+'\n')
                new_types_all.append(new_types)
            def strize(x):
                if isinstance(x, UnionType):
                    return '/'.join([str(y) for y in x.items])
                return str(x)
            def rank(l, x):
                if x in l:
                    return l.index(x)
                else:
                    return 1000000
            def topize(l):
                ret = []
                for x in l:
                    if x not in ret:
                        ret.append(x)
                    if len(ret) == 3:
                        return ret
                return ret
            strs = []
            rets = []
            origin_rets = [x.ret_type for x in items]
            topn = sorted(origin_rets, key = lambda x:rank(new_types_all[-1], identity(x)))
            top3 = topize(topn)
            rets = [strize(x) for x in top3]
            ret_str = '/'.join(rets)
            strs.append(ret_str)
            for i, a in enumerate(func.arguments):
                if is_method and i == 0 :
                    continue
                origin_args = [x.arg_types[i] for x in items]
                topn = sorted(origin_args, key = lambda x:rank(new_types_all[i], identity(x)))
                top3 = topize(topn)
                args = [strize(x) for x in top3]
                arg_str = '/'.join(args)
                strs.append(arg_str)
            self.func_name_recorder[func.fullname] = strs
            return
            self.result_file.write(annotation+'\n\n')
        self.var_node = {k:v for k,v in original_var_node.items()}
        self.dp_dag = {k:v for k,v in original_dp_dag.items()}
        self.type_map = {k:v for k,v in original_type_map.items()}
        self.wide_type_map = {k:v for k,v in original_wide_type_map.items()}
        self.expr_checker.local_infer_map = {k:v for k,v in original_infer_map.items()}
        for arg in func.arguments:
            self.tv_level[arg].clear()
        self.record = {}
        return True
    def in_var_node(self, node, var_node=None):
        if not (isinstance(node, str) or isinstance(node,tuple)):
            var = literal_hash(node)
        else:
            var = node
        if  var_node is not None:
            return var in var_node    
        return var in self.var_node
    def get_var_node(self, node, var_node=None):
        if not (isinstance(node, str) or isinstance(node,tuple)):
            var = literal_hash(node)
        else:
            var = node
        if  var_node is not None:
            return var_node[var]
        return self.var_node[var]
    def update_var_node(self, node, var_node=None):
        if not (isinstance(node, str) or isinstance(node,tuple)):
            var = literal_hash(node)
        else:
            var = node
        if var_node is not None:
            var_node[var] = node
        self.var_node[var] = node
    def setS1(self, s1):
        self.s1 = s1
    def setS2(self, s2):
        self.s2 = list(set(s2))
    def setS3(self, s3):
        self.s3 = list(set(s3))
    def set_hierarchy(self, hierarchy_children):
        self.hierarchy_children = hierarchy_children
    def set_user_defined(self, user_defined):
        self.user_defined = list(set(user_defined))
    def setS4(self, s4):
        self.s4 = list(set(s4))
    def makeS1Type(self):
        return self.S1()
    def makeS2Type(self):
        return self.S2()
    def makeS3Type(self, t=None):
        if t:
            t = t.items[0]
            s3 = [x for x in self.S3() if is_subtype(x, t)]
            return s3
        return self.S3()
    def makeS4Type(self, t=None):
        if t and len(t.items) == 1: 
            t = t.items[0]
            s4 = [x for x in self.S4() if is_subtype(x, t)]
            return s4
        return self.S4()
    def new_type_var(self, arg, directly_object=False):
        object_type = self.named_type('builtins.object')
        if directly_object:
            return object_type
        bounded_name = [x.name for x in self.record]
        for i in range(100):
            new_name = f'T{i}'
            if new_name not in bounded_name:
                tv = TypeVarType(f'T{i}', f'T{i}', i, [], object_type)
                self.record[tv] = arg
                return tv
    def S1(self, node, arg, candidates=None):
        return self.func_s1[node][arg]
    def S2(self, node, arg, candidates=None):
        return self.func_s2[node][arg].union(self.S1(node, arg))
    def S3_for(self, node, arg, t1):
        if not isinstance(t1, Instance):
            return set()
        s3_for = set()
        for t2 in self.S3(node, arg):
            if isinstance(t2, Instance) and t2.type == t1.type:
                s3_for.add(t2)
        if t1 in self.hierarchy_children:
            s3_for.update(self.hierarchy_children[t1])
        return s3_for
    def S3(self, node, arg, candidates=None, ground=None):
        return self.S2(node, arg).union(self.func_s3[node][arg])
    def S4(self, candidates=None, ground=None):
        return self.s4
    def check_first_pass(self) -> None:
        """Type check the entire file, but defer functions with unresolved references.
        Unresolved references are forward references to variables
        whose types haven't been inferred yet.  They may occur later
        in the same file or in a different file that's being processed
        later (usually due to an import cycle).
        Deferred functions will be processed by check_second_pass().
        """
        import datasets.filesystems.compression
        self.recurse_into_functions = True
        self.is_checking = True
        with state.strict_optional_set(self.options.strict_optional):
            self.errors.set_file(self.path, self.tree.fullname, scope=self.tscope)
            with self.tscope.module_scope(self.tree.fullname):
                with self.binder.top_frame_context():
                    for d in self.tree.defs:
                        self.accept(d)
                assert not self.current_node_deferred
    def check_second_pass(self,
                          todo: Optional[Sequence[Union[DeferredNode,
                                                        FineGrainedDeferredNode]]] = None
                          ) -> bool:
        """Run second or following pass of type checking.
        This goes through deferred nodes, returning True if there were any.
        """
        self.recurse_into_functions = True
        with state.strict_optional_set(self.options.strict_optional):
            if not todo and not self.deferred_nodes:
                return False
            self.errors.set_file(self.path, self.tree.fullname, scope=self.tscope)
            with self.tscope.module_scope(self.tree.fullname):
                self.pass_num += 1
                if not todo:
                    todo = self.deferred_nodes
                else:
                    assert not self.deferred_nodes
                self.deferred_nodes = []
                done: Set[Union[DeferredNodeType, FineGrainedDeferredNodeType]] = set()
                for node, active_typeinfo in todo:
                    if node in done:
                        continue
                    done.add(node)
                    with self.tscope.class_scope(active_typeinfo) if active_typeinfo \
                            else nothing():
                        with self.scope.push_class(active_typeinfo) if active_typeinfo \
                                else nothing():
                            self.check_partial(node)
            return True
    def set_candidates(self, candidates):
        self.candidates = candidates
    def suggest_first_pass(self, init=False) -> None:
        self.recurse_into_functions = True
        with state.strict_optional_set(self.options.strict_optional):
            self.errors.set_file(self.path, self.tree.fullname, scope=self.tscope)
            with self.tscope.module_scope(self.tree.fullname):
                with self.binder.top_frame_context():
                    for i, d in enumerate(self.tree.defs):
                        if isinstance(d, FuncDef):
                            if self.mode == 'CPA':
                                self.suggest_function_CPA(d, init=init)
                            else:
                                self.suggest_function(d, init=init)
                        elif isinstance(d, Decorator):
                            if self.mode == 'CPA':
                                self.suggest_function_CPA(d.func)
                            else:
                                self.suggest_function(d.func, init=init)
                        elif isinstance(d, ClassDef):
                            self.suggest_class(d, init=init)
                        elif isinstance(d, AssignmentStmt):
                            self.visit_assignment_stmt(d)
                        else:
                            self.accept(d)
    def suggest_second_pass(self,
                          todo: Optional[Sequence[Union[DeferredNode,
                                                        FineGrainedDeferredNode]]] = None
                          ) -> bool:
        self.recurse_into_functions = True
        with state.strict_optional_set(self.options.strict_optional):
            if not todo and not self.deferred_nodes:
                return False
            self.errors.set_file(self.path, self.tree.fullname, scope=self.tscope)
            with self.tscope.module_scope(self.tree.fullname):
                with self.binder.top_frame_context():
                    self.pass_num += 1
                    if not todo:
                        todo = self.deferred_nodes
                    else:
                        assert not self.deferred_nodes
                    self.deferred_nodes = []
                    done: Set[Union[DeferredNodeType, FineGrainedDeferredNodeType]] = set()
                    for i, (node, active_typeinfo) in enumerate(todo):
                        if node in done:
                            continue
                        done.add(node)
                        if isinstance(node, FuncDef):
                            with self.tscope.class_scope(active_typeinfo) if active_typeinfo \
                                    else nothing():
                                with self.scope.push_class(active_typeinfo) if active_typeinfo \
                                        else nothing():
                                            if self.mode == 'CPA':
                                                self.suggest_function_CPA(node)
                                            else:
                                                self.suggest_function(node)
            return True
    def defer_node(self, node: DeferredNodeType, enclosing_class: Optional[TypeInfo]) -> None:
        self.deferred_nodes.append(DeferredNode(node, enclosing_class))
    def handle_cannot_determine_type(self, name: str, context: Context) -> None:
        if self.is_checking:
            return
        node = self.scope.top_non_lambda_function()
        if node not in self.func_candidates:
            return 
        if isinstance(node, FuncDef):
            enclosing_class = self.scope.enclosing_class()
            self.defer_node(node, enclosing_class)
            self.current_node_deferred = True
            self.defer_this_node = True
        else:
            pass
    def accept(self, stmt: Statement) -> None:
        self.manager.lexical_stat[type(stmt)].add(stmt)
        stmt.accept(self)
    def accept_loop(self, body: Statement, else_body: Optional[Statement] = None, *,
                    exit_condition: Optional[Expression] = None) -> None:
        with self.binder.frame_context(can_skip=False, conditional_frame=True):
            while True:
                with self.binder.frame_context(can_skip=True,
                                               break_frame=2, continue_frame=1):
                    self.accept(body)
                if not self.binder.last_pop_changed or True:
                    break
            if exit_condition:
                _, else_map = self.find_isinstance_check(exit_condition)
                self.push_type_map(else_map)
            if else_body:
                self.accept(else_body)
    def visit_overloaded_func_def(self, defn: OverloadedFuncDef) -> None:
        return
    def visit_func_def(self, defn: FuncDef) -> None:
        self.manager.lexical_stat[type(defn)].add(defn)
        if self.node is not None and self.node.info and (defn.name != '__init__' and defn != self.node):
            return
        if not self.recurse_into_functions:
            return
        with self.tscope.function_scope(defn):
            self._visit_func_def(defn)
    def _visit_func_def(self, defn: FuncDef) -> None:
        self.check_func_item(defn) 
    def check_func_item(self, defn: FuncItem) -> None:
        """Type check a function.
        If type_override is provided, use it as the function type.
        """
        typ = self.function_type(defn)
        if isinstance(typ, CallableType):
            self.check_func_def(defn, typ)
        else:
            raise RuntimeError('Not supported')
        self.current_node_deferred = False
    def check_func_def(self, defn: FuncItem, typ: CallableType) -> None:
        expanded = self.expand_typevars(defn, typ)
        for item, typ in expanded:
            old_binder = self.binder
            self.binder = ConditionalTypeBinder(self)
            with self.binder.top_frame_context():
                defn.expanded.append(item)
                self.return_types.append(typ.ret_type)
                for i in range(len(typ.arg_types)):
                    arg_type = typ.arg_types[i]
                    if typ.arg_kinds[i] == nodes.ARG_STAR:
                        arg_type = self.named_generic_type('builtins.tuple',
                                                           [arg_type])
                    elif typ.arg_kinds[i] == nodes.ARG_STAR2:
                        arg_type = self.named_generic_type('builtins.dict',
                                                           [self.str_type(),
                                                            arg_type])
                    self.update_var_node(item.arguments[i])
                    self.store_type(item.arguments[i], arg_type)
                body_is_trivial = self.is_trivial_body(defn.body)
                self.check_default_args(item, body_is_trivial)
            with self.binder.top_frame_context():
                with self.scope.push_function(defn):
                    if len(expanded) >= 2:
                        self.binder.suppress_unreachable_warnings()
                    self.accept(item.body)
                unreachable = self.binder.is_unreachable()
            self.return_types.pop()
            self.binder = old_binder
    def check_default_args(self, item: FuncItem, body_is_trivial: bool) -> None:
        for arg in item.arguments:
            if arg.initializer is None:
                continue
            if body_is_trivial and isinstance(arg.initializer, EllipsisExpr):
                continue
            name = arg.variable.name
            if arg in self.type_map:
                self.check_completed_assignment(
                    self.type_map[arg],
                    arg.initializer,
                    context=arg.initializer, lvalue=arg)
            else:
                continue
    def is_trivial_body(self, block: Block) -> bool:
        """Returns 'true' if the given body is "trivial" -- if it contains just a "pass",
        "..." (ellipsis), or "raise NotImplementedError()". A trivial body may also
        start with a statement containing just a string (e.g. a docstring).
        Note: functions that raise other kinds of exceptions do not count as
        "trivial". We use this function to help us determine when it's ok to
        relax certain checks on body, but functions that raise arbitrary exceptions
        are more likely to do non-trivial work. For example:
           def halt(self, reason: str = ...) -> NoReturn:
               raise MyCustomError("Fatal error: " + reason, self.line, self.context)
        A function that raises just NotImplementedError is much less likely to be
        this complex.
        """
        body = block.body
        if (body and isinstance(body[0], ExpressionStmt) and
                isinstance(body[0].expr, (StrExpr, UnicodeExpr))):
            body = block.body[1:]
        if len(body) == 0:
            return True
        elif len(body) > 1:
            return False
        stmt = body[0]
        if isinstance(stmt, RaiseStmt):
            expr = stmt.expr
            if expr is None:
                return False
            if isinstance(expr, CallExpr):
                expr = expr.callee
            return (isinstance(expr, NameExpr)
                    and expr.fullname == 'builtins.NotImplementedError')
        return (isinstance(stmt, PassStmt) or
                (isinstance(stmt, ExpressionStmt) and
                 isinstance(stmt.expr, EllipsisExpr)))
    def expand_typevars(self, defn: FuncItem,
                        typ: CallableType) -> List[Tuple[FuncItem, CallableType]]:
        subst: List[List[Tuple[TypeVarId, Type]]] = []
        tvars = list(typ.variables) or []
        if defn.info:
            tvars += defn.info.defn.type_vars or []
        for tvar in tvars:
            if isinstance(tvar, TypeVarType) and tvar.values:
                subst.append([(tvar.id, value) for value in tvar.values])
        if subst and not self.options.mypyc:
            result: List[Tuple[FuncItem, CallableType]] = []
            for substitutions in itertools.product(*subst):
                mapping = dict(substitutions)
                expanded = cast(CallableType, expand_type(typ, mapping))
                result.append((expand_func(defn, mapping), expanded))
            return result
        else:
            return [(defn, typ)]
    def bind_and_map_method(self, sym: SymbolTableNode, typ: FunctionLike,
                            sub_info: TypeInfo, super_info: TypeInfo) -> FunctionLike:
        """Bind self-type and map type variables for a method.
        Arguments:
            sym: a symbol that points to method definition
            typ: method type on the definition
            sub_info: class where the method is used
            super_info: class where the method was defined
        """
        if (isinstance(sym.node, (FuncDef, OverloadedFuncDef, Decorator))
                and not is_static(sym.node)):
            if isinstance(sym.node, Decorator):
                is_class_method = sym.node.func.is_class
            else:
                is_class_method = sym.node.is_class
            bound = bind_self(typ, self.scope.active_self_type(), is_class_method)
        else:
            bound = typ
        return cast(FunctionLike, map_type_from_supertype(bound, sub_info, super_info))
    def visit_class_def(self, defn: ClassDef) -> None:
        self.manager.lexical_stat[type(defn)].add(defn)
        typ = defn.info
        with self.tscope.class_scope(defn.info):
            old_binder = self.binder
            self.binder = ConditionalTypeBinder(self)
            with self.binder.top_frame_context():
                with self.scope.push_class(defn.info):
                    self.accept(defn.defs)
            self.binder = old_binder
    def visit_block(self, b: Block) -> None:
        original_var_node = {k:v for k,v in self.var_node.items()}
        if b.is_unreachable:
            self.binder.unreachable()
            return
        for s in b.body:
            if self.binder.is_unreachable():
                break
            self.accept(s)
    def visit_assignment_stmt(self, s: AssignmentStmt) -> None:
        """Type check an assignment statement.
        Handle all kinds of assignment statements (simple, indexed, multiple).
        """
        if not (s.is_alias_def and self.is_stub):
            with self.enter_final_context(s.is_final_def):
                self.check_assignment(s.lvalues[-1], s.rvalue, s.type is None, s.new_syntax)
        if len(s.lvalues) > 1:
            if s.rvalue not in self.type_map:
                self.expr_checker.accept(s.rvalue)
            rvalue = self.temp_node(self.type_map[s.rvalue], s)
            for lv in s.lvalues[:-1]:
                with self.enter_final_context(s.is_final_def):
                    self.check_assignment(lv, rvalue, s.type is None)
    def check_assignment(self, lvalue: Lvalue, rvalue: Expression, infer_lvalue_type: bool = True,
                         new_syntax: bool = False) -> None:
        if isinstance(lvalue, TupleExpr) or isinstance(lvalue, ListExpr):
            self.check_assignment_to_multiple_lvalues(lvalue.items, rvalue, rvalue,
                                                      infer_lvalue_type)
        else:
            lvalue_type, index_lvalue, inferred, lvar, temp_lnode = self.check_lvalue(lvalue)
            if lvalue_type:
                if (isinstance(lvalue, MemberExpr) and
                        lvalue.kind is None):
                    self.check_member_assignment(lvalue_type, rvalue, context=rvalue, lvalue=lvalue, lnode = temp_lnode, lvar=lvar)
                else:
                    self.check_completed_assignment(lvalue_type, rvalue, context=rvalue, lvalue=lvalue)
            elif index_lvalue:
                self.check_indexed_assignment(index_lvalue, rvalue, lvalue)
            if inferred:
                if inferred.type is not None:
                    return
                rvalue_type = self.expr_checker.accept(rvalue)
                rtypes = self.type_map[rvalue]
                ltypes = []
                for rtype in rtypes:
                    maybe_partial = self.infer_partial_type_for_rtype(lvalue, rtype)
                    ltypes.append(maybe_partial)
                    self.expr_checker.add_infer_type((lvalue, maybe_partial),[(rvalue, rtype)])
                self.store_type(lvalue, ltypes)
                self.update_var_node(lvalue)
    def get_final_context(self) -> bool:
        return self._is_final_def
    @contextmanager
    def enter_final_context(self, is_final_def: bool) -> Iterator[None]:
        old_ctx = self._is_final_def
        self._is_final_def = is_final_def
        try:
            yield
        finally:
            self._is_final_def = old_ctx
    def check_assignment_to_multiple_lvalues(self, lvalues: List[Lvalue], rvalue: Expression,
                                             context: Context,
                                             infer_lvalue_type: bool = True) -> None:
        if isinstance(rvalue, TupleExpr) or isinstance(rvalue, ListExpr):
            rvalues: List[Expression] = []
            iterable_type: Optional[Type] = None
            last_idx: Optional[int] = None
            for idx_rval, rval in enumerate(rvalue.items):
                if isinstance(rval, StarExpr):
                    typs = self.expr_checker.visit_star_expr(rval).type
                    if isinstance(typs, TupleType):
                        rvalues.extend([TempNode(typ) for typ in typs.items])
                else:
                    rvalues.append(rval)
            iterable_start: Optional[int] = None
            iterable_end: Optional[int] = None
            for i, rval in enumerate(rvalues):
                if isinstance(rval, StarExpr):
                    typs = self.expr_checker.visit_star_expr(rval).type
                    if self.type_is_iterable(typs) and isinstance(typs, Instance):
                        if iterable_start is None:
                            iterable_start = i
                        iterable_end = i
            if (iterable_start is not None
                    and iterable_end is not None
                    and iterable_type is not None):
                iterable_num = iterable_end - iterable_start + 1
                rvalue_needed = len(lvalues) - (len(rvalues) - iterable_num)
                if rvalue_needed > 0:
                    rvalues = rvalues[0: iterable_start] + [TempNode(iterable_type)
                        for i in range(rvalue_needed)] + rvalues[iterable_end + 1:]
            if self.check_rvalue_count_in_assignment(lvalues, len(rvalues), context):
                star_index = next((i for i, lv in enumerate(lvalues) if
                                   isinstance(lv, StarExpr)), len(lvalues))
                left_lvs = lvalues[:star_index]
                star_lv = cast(StarExpr,
                               lvalues[star_index]) if star_index != len(lvalues) else None
                right_lvs = lvalues[star_index + 1:]
                left_rvs, star_rvs, right_rvs = self.split_around_star(
                    rvalues, star_index, len(lvalues))
                lr_pairs = list(zip(left_lvs, left_rvs))
                if star_lv:
                    rv_list = ListExpr(star_rvs)
                    rv_list.set_line(rvalue.get_line())
                    lr_pairs.append((star_lv.expr, rv_list))
                lr_pairs.extend(zip(right_lvs, right_rvs))
                for lv, rv in lr_pairs:
                    self.check_assignment(lv, rv, infer_lvalue_type)
        else:
            self.check_multi_assignment(lvalues, rvalue, context, infer_lvalue_type)
    def check_rvalue_count_in_assignment(self, lvalues: List[Lvalue], rvalue_count: int,
                                         context: Context) -> bool:
        if any(isinstance(lvalue, StarExpr) for lvalue in lvalues):
            if len(lvalues) - 1 > rvalue_count:
                return False
        elif rvalue_count != len(lvalues):
            return False
        return True
    def check_multi_assignment(self, lvalues: List[Lvalue],
                               rvalue: Expression,
                               context: Context,
                               infer_lvalue_type: bool = True,
                               rv_type: Set[Type] = None,
                               undefined_rvalue: bool = False) -> None:
        """Check the assignment of one rvalue to a number of lvalues.
        a,*b,c,d... = t1
        case T[t1]:
        | Tuple
        | Iterable
        | Union
        | Any
        """
        rvalue_types = rv_type or self.expr_checker.accept(rvalue)
        ltypes_store = defaultdict(list)
        for rvalue_type in rvalue_types:
            ltypes = self.check_multiple_from_multiple_types(lvalues, rvalue, context, infer_lvalue_type, rvalue_type)
            for lvalue, ltype in zip(lvalues, ltypes):
                if isinstance(lvalue, StarExpr):
                    lvalue = lvalue.expr
                self.expr_checker.add_infer_type((lvalue, ltype), [(rvalue, rvalue_type)])
                ltypes_store[lvalue].append(ltype)
        for lvalue in ltypes_store:
            if isinstance(lvalue, StarExpr):
                lvalue = lvalue.expr
            self.update_var_node(lvalue)
            self.store_type(lvalue, ltypes_store[lvalue])
    def check_multiple_from_multiple_types(self, lvalues: List[Lvalue],
                                rvalue: Expression,
                                context: Context,
                                infer_lvalue_type: bool = True,
                                rv_type: Set[Type] = None,) -> None:
        """
            types(lv, rt)
            match rt with
            | Tuple
            | Iterable
            | Union -> Union[types(lv,r)]
            | Any
        """
        rvalue_type = rv_type
        if isinstance(rvalue_type, UnionType):
            relevant_items = rvalue_type.relevant_items()
            if len(relevant_items) == 1:
                rvalue_type = relevant_items[0]
        if isinstance(rvalue_type, AnyType):
            return [AnyType(0)] * len(lvalues)
        elif isinstance(rvalue_type, TupleType):
            return self.check_multi_assignment_from_tuple(lvalues, rvalue, rvalue_type,
                                                context, True, infer_lvalue_type)
        elif isinstance(rvalue_type, UnionType):
            stores = defaultdict(list)
            for item in rvalue_type.items:
                ltypes_item =  self.check_multiple_from_multiple_types(lvalues, rvalue, context,
                                                infer_lvalue_type, item)
                for i, _ in enumerate(ltypes_item):
                    stores[i].append(_)
            return [UnionType.make_union(x) for x in stores.values()]
        else:
            if self.type_is_iterable(rvalue_type) and isinstance(rvalue_type, Instance):
                return self.check_multi_assignment_from_iterable(lvalues, rvalue_type, rvalue, 
                                                        context, infer_lvalue_type)
            else:
                self.expr_checker.add_single_incompatible(rvalue, rvalue_type)
                return [AnyType(0)] * len(lvalues)
    def check_multi_assignment_from_union(self, lvalues: List[Expression], rvalue: Expression,
                                          rvalue_type: UnionType, context: Context,
                                          infer_lvalue_type: bool) -> None:
        # assert False, "union is not finished"
        return
    def check_multi_assignment_from_tuple(self, lvalues: List[Lvalue], rvalue: Expression,
                                          rvalue_type: TupleType, context: Context,
                                          undefined_rvalue: bool,
                                          infer_lvalue_type: bool = True) -> None:
        """
        a,*b,c,d,.. = e
        len(e) >= len([a,c,d..])
        """
        if self.check_rvalue_count_in_assignment(lvalues, len(rvalue_type.items), context):
            star_index = next((i for i, lv in enumerate(lvalues)
                               if isinstance(lv, StarExpr)), len(lvalues))
            left_lvs = lvalues[:star_index]
            star_lv = cast(StarExpr, lvalues[star_index]) if star_index != len(lvalues) else None
            right_lvs = lvalues[star_index + 1:]
            left_rv_types, star_rv_types, right_rv_types = self.split_around_star(
                rvalue_type.items, star_index, len(lvalues))
            if star_lv:
                list_expr = ListExpr([self.temp_node(rv_type, context)
                                      for rv_type in star_rv_types])
                list_expr.set_line(context.get_line())
                list_type = self.expr_checker.accept(list_expr)[0]
                return list(left_rv_types) + [list_type] + list(right_rv_types)
            else:
                return list(left_rv_types) + list(right_rv_types)
        else:
            # assert False, "todo"
            return [AnyType(0)] * len(lvalues)
    def split_around_star(self, items: List[T], star_index: int,
                          length: int) -> Tuple[List[T], List[T], List[T]]:
        """Splits a list of items in three to match another list of length 'length'
        that contains a starred expression at 'star_index' in the following way:
        star_index = 2, length = 5 (i.e., [a,b,*,c,d]), items = [1,2,3,4,5,6,7]
        returns in: ([1,2], [3,4,5], [6,7])
        """
        nr_right_of_star = length - star_index - 1
        right_index = -nr_right_of_star if nr_right_of_star != 0 else len(items)
        left = items[:star_index]
        star = items[star_index:right_index]
        right = items[right_index:]
        return left, star, right
    def type_is_iterable(self, type: Type) -> bool:
        if isinstance(type, CallableType) and type.is_type_obj():
            type = type.fallback
        return is_subtype(type, self.named_generic_type('typing.Iterable',
                                                        [AnyType(TypeOfAny.special_form)]))
    def check_multi_assignment_from_iterable(self, lvalues: List[Lvalue], rvalue_type: Type, rvalue, 
                                             context: Context,
                                             infer_lvalue_type: bool = True) -> None:
        ret = []
        if self.type_is_iterable(rvalue_type) and isinstance(rvalue_type, Instance):
            for lv in lvalues:
                item_type = self.iterable_item_type(rvalue_type)
                if isinstance(lv, StarExpr):
                    item_type = self.named_generic_type('builtins.list', [item_type])
                ret.append(item_type)
        else:
            self.msg.type_not_iterable(rvalue_type, context)
        return ret
    def check_lvalue(self, lvalue: Lvalue):
        lvalue_type = None
        index_lvalue = None
        inferred = None
        var = None
        temp_lnode = None
        if self.is_definition(lvalue) and (
            not isinstance(lvalue, NameExpr) or isinstance(lvalue.node, Var)
        ):
            if isinstance(lvalue, NameExpr):
                inferred = cast(Var, lvalue.node)
                assert isinstance(inferred, Var)
            else:
                assert isinstance(lvalue, MemberExpr)
                self.expr_checker.accept(lvalue.expr)
                inferred = lvalue.def_var
        elif isinstance(lvalue, IndexExpr):
            index_lvalue = lvalue
        elif isinstance(lvalue, MemberExpr):
            lvalue_type = self.expr_checker.analyze_ordinary_member_access(lvalue, True)
            if hasattr(lvalue.expr, "name") and lvalue.expr.name == 'self':
                node_type = self.expr_checker.accept(lvalue.expr)
                node_type = node_type.items[0] if isinstance(node_type, MaybeTypes) else node_type
                if hasattr(node_type,"type"):
                    info = node_type.type
                    var = lookup_member_var_or_accessor(info, lvalue.name, True)
        elif isinstance(lvalue, NameExpr):
            lvalue_type = self.expr_checker.analyze_ref_expr(lvalue, lvalue=True)
            var = lvalue.node
        elif isinstance(lvalue, TupleExpr) or isinstance(lvalue, ListExpr):
            types = [self.check_lvalue(sub_expr)[0] or
                     UninhabitedType() for sub_expr in lvalue.items]
            lvalue_type = TupleType(types, self.named_type('builtins.tuple'))
        elif isinstance(lvalue, StarExpr):
            typ, _1, _2, _3, _4 = self.check_lvalue(lvalue.expr)
            lvalue_type = StarType(typ) if typ else None
        else:
            lvalue_type = self.expr_checker.accept(lvalue)
        return lvalue_type, index_lvalue, inferred, var, temp_lnode
    def is_definition(self, s: Lvalue) -> bool:
        if isinstance(s, NameExpr):
            node = s.node
            if isinstance(node, Var):
                return not self.in_var_node(s)
        elif isinstance(s, MemberExpr):
            return s.is_inferred_def
        return False
    def infer_partial_type_for_rtype(self, lvalue, init_type):
        if not is_valid_inferred_type(init_type):
            return self.infer_partial_type_for_rtype_inner(lvalue, init_type)
        else:
            return init_type
    def infer_partial_type_for_rtype_inner(self, lvalue: Lvalue, init_type: Type) -> bool:
        partial_type = init_type
        if isinstance(init_type, NoneType):
            partial_type = PartialType(None, None)
        elif isinstance(init_type, Instance):
            fullname = init_type.type.fullname
            is_ref = isinstance(lvalue, RefExpr)
            if (is_ref and
                    (fullname == 'builtins.list' or
                     fullname == 'builtins.set' or
                     fullname == 'builtins.dict' or
                     fullname == 'collections.OrderedDict') and
                    all(isinstance(t, (NoneType, UninhabitedType))
                        for t in init_type.args)):
                partial_type = PartialType(init_type.type, None)
            elif is_ref and fullname == 'collections.defaultdict':
                arg0 = init_type.args[0]
                arg1 = init_type.args[1]
                if (isinstance(arg0, (NoneType, UninhabitedType)) and
                        self.is_valid_defaultdict_partial_value_type(arg1)):
                    arg1 = erase_type(arg1)
                    assert isinstance(arg1, Instance)
                    partial_type = PartialType(init_type.type, None, arg1)
                else:
                    return partial_type
            else:
                return partial_type
        else:
            return partial_type
        return partial_type
    def infer_partial_type(self, name: Var, lvalue: Lvalue, init_type: Type) -> bool:
        partial_type = init_type
        if isinstance(init_type, NoneType):
            partial_type = PartialType(None, name)
        elif isinstance(init_type, Instance):
            fullname = init_type.type.fullname
            is_ref = isinstance(lvalue, RefExpr)
            if (is_ref and
                    (fullname == 'builtins.list' or
                     fullname == 'builtins.set' or
                     fullname == 'builtins.dict' or
                     fullname == 'collections.OrderedDict') and
                    all(isinstance(t, (NoneType, UninhabitedType))
                        for t in init_type.args)):
                partial_type = PartialType(init_type.type, name)
            elif is_ref and fullname == 'collections.defaultdict':
                arg0 = init_type.args[0]
                arg1 = init_type.args[1]
                if (isinstance(arg0, (NoneType, UninhabitedType)) and
                        self.is_valid_defaultdict_partial_value_type(arg1)):
                    arg1 = erase_type(arg1)
                    assert isinstance(arg1, Instance)
                    partial_type = PartialType(init_type.type, name, arg1)
                else:
                    return False, partial_type
            else:
                return False, partial_type
        else:
            return False, partial_type
        self.set_inferred_type(name, lvalue, partial_type)
        self.partial_types[-1].map[name] = lvalue
        return True, partial_type
    def is_valid_defaultdict_partial_value_type(self, t: ProperType) -> bool:
        """Check if t can be used as the basis for a partial defaultdict value type.
        Examples:
          * t is 'int' --> True
          * t is 'list[<nothing>]' --> True
          * t is 'dict[...]' --> False (only generic types with a single type
            argument supported)
        """
        if not isinstance(t, Instance):
            return False
        if len(t.args) == 0:
            return True
        if len(t.args) == 1:
            arg = t.args[0]
            if isinstance(arg, (TypeVarType, UninhabitedType, NoneType)):
                return True
        return False
    def set_inferred_type(self, var: Var, lvalue: Lvalue, type: Set[Type]) -> None:
        """Store inferred variable type.
        Store the type to both the variable node and the expression node that
        refers to the variable (lvalue). If var is None, do nothing.
        """
        if var:
            self.update_var_node(var, lvalue)
            var.is_inferred = True
            if var not in self.var_decl_frames:
                self.var_decl_frames[var] = {frame.id for frame in self.binder.frames}
            if isinstance(lvalue, MemberExpr) and self.inferred_attribute_types is not None:
                if lvalue.def_var is not None:
                    self.inferred_attribute_types[lvalue.def_var] = type
            self.store_type(lvalue, type)
    def check_completed_assignment(self, lvalue_types: Set[Type], rvalue: Expression,
                                context: Context, lvalue = None) -> None:
        if self.is_checking:
            return
        rvalue_types = self.expr_checker.accept(rvalue)
        for lvalue_type in lvalue_types:
            for rvalue_type in rvalue_types:
                if self.check_subtype(rvalue_type, lvalue_type,context):
                    pass
                else:
                    self.expr_checker.add_improvement_from_pair(lvalue, lvalue_type)
                    self.expr_checker.add_incompatible(lvalue, lvalue_type, rvalue, rvalue_type)
    def check_member_assignment(self, attribute_type: Set[Type], rvalue: Expression, context: Context, lvalue=None, lnode=None, lvar=None) -> None:
        """Type member assignment.
        """
        rvalue_type = self.check_completed_assignment(attribute_type, rvalue, context, lvalue=lvalue)
    def check_indexed_assignment(self, lvalue: IndexExpr,
                                 rvalue: Expression, context: Context) -> None:
        """Type check indexed assignment base[index] = rvalue.
        The lvalue argument is the base[index] expression.
        """
        self.try_infer_partial_type_from_indexed_assignment(lvalue, rvalue)
        basetype = self.expr_checker.accept(lvalue.base)
        method_node = TempNode(AnyType(0), context)
        self.expr_checker.check_method_call_by_name('__setitem__', basetype, [lvalue.index, rvalue],
        [nodes.ARG_POS, nodes.ARG_POS], context, object_node = context.base, method_node = method_node, return_node = context)
    def try_infer_partial_type_from_indexed_assignment(
            self, lvalue: IndexExpr, rvalue: Expression) -> None:
        """
            |>i:kt    |> b:vt     x:PDict i:kt b:vt 
           -------    --------    -------------------  
            i:kt       b:vt      x:Dict[kt,vt]     
        -----------------------------------------------------
            x[i] = b:unit 
        """
        var = None
        if isinstance(lvalue.base, RefExpr) and isinstance(lvalue.base.node, Var):
            node = lvalue.base
            inferred_types = []
            if self.in_var_node(node):
                def_node = self.get_var_node(node)
                types = self.type_map[def_node]
                for typ in types:
                    if isinstance(typ, PartialType) and typ.type is not None:
                        type_type = typ.type
                        typename = type_type.fullname
                        if (typename == 'builtins.dict'
                                or typename == 'collections.OrderedDict'
                                or typename == 'collections.defaultdict'):
                            key_types = self.expr_checker.accept(lvalue.index)
                            value_types = self.expr_checker.accept(rvalue)
                            for key_type in key_types:
                                for value_type in value_types:
                                    inferred_type = self.named_generic_type(typename, [key_type, value_type])
                                    inferred_types.append(inferred_type)
                                    self.expr_checker.add_infer_type((node, inferred_type), [(def_node, typ), (lvalue.index, key_type), (rvalue, value_type)])
                    else:
                        inferred_type = typ
                        inferred_types.append(inferred_type)
                        self.expr_checker.add_infer_type((node, typ), [(def_node, typ)])
                self.update_var_node(node)
                self.store_type(node, inferred_types)
    def visit_expression_stmt(self, s: ExpressionStmt) -> None:
         self.expr_checker.accept(s.expr)
    def update_infer_dependency_map_with_constraint_pairs(self, identity, typ, constraint_pairs):
        try:
            ground_pairs = get_ground_pairs(self.dp_dag, self.expr_checker.local_infer_map, constraint_pairs, self.combination_limits)
        except RecursionError:
            pass
        get_ground_pairs(self.dp_dag, self.expr_checker.local_infer_map, constraint_pairs, self.combination_limits)
        for possible_ground in ground_pairs:
            # possible_ground = [(node, typ) for node, typ in possible_ground if isinstance(node, Argument)]
            self.update_infer_dependency_map((identity, typ), possible_ground)
    def update_infer_dependency_map_with_pairs(self, identity, typ, possible_pairs):
        identity_pairs = []
        for pair in possible_pairs:
            self.update_infer_dependency_map_with_constraint_pairs(identity, typ, [pair])
    def update_infer_dependency_map_from_local(self, expr):
        if self.current_node_deferred:
            return
        flag = 0
        for key in self.expr_checker.local_infer_map:
            node, typ = key
            if node == expr:
                flag = 1
                for possible_pairs in list(self.expr_checker.local_infer_map[key])[:self.combination_limits]:
                    self.update_infer_dependency_map_with_constraint_pairs(node, typ, possible_pairs)
        if flag == 0 and expr in self.type_map:
            rets = self.type_map[expr]
            for r in rets:
                self.update_infer_dependency_map((expr, r), [])
    def visit_return_stmt(self, s: ReturnStmt) -> None:
        self.check_return_stmt(s)
        if s.expr is not None and not self.is_checking and not isinstance(self.scope.top_function(), LambdaExpr) and self.scope.top_function() == self.current_node:
            self.update_infer_dependency_map_from_local(s.expr)
        self.binder.unreachable()
    def check_return_stmt(self, s: ReturnStmt) -> None:
        defn = self.scope.top_function()
        if defn is not None:
            return_type = self.return_types[-1]
            if s.expr:
                typ = self.expr_checker.accept(s.expr, return_type)
    def update_type_map(self, type_map):
        for k in type_map:
            self.update_var_node(k)
            self.store_type(k, type_map[k])
    def visit_if_stmt(self, s: IfStmt) -> None:
        total_else_map = {}
        condition_num = len(s.expr)
        all_var_node = {k:v for k,v in self.var_node.items()}
        with self.binder.frame_context(can_skip=False, conditional_frame=True, fall_through=0):
            for i, (e, b) in enumerate(zip(s.expr, s.body)):
                t = self.expr_checker.accept(e)
                original_type_hook = {k:v for k,v in self.type_hook.items()}
                if_map, else_map = self.find_isinstance_check(e)
                bool_instance = self.expr_checker.bool_type()
                true_literal = LiteralType(value=True, fallback=bool_instance)
                false_literal = LiteralType(value=False, fallback=bool_instance)
                if_node = FlowNode(true_literal, e)
                else_node = FlowNode(false_literal, e)
                original_var_node = {k:v for k,v in self.var_node.items()}
                with self.binder.frame_context(can_skip=True, fall_through=2):
                    self.push_type_map(if_map, if_node, true_literal)
                    self.accept(b)
                for var in self.var_node:
                    if var not in all_var_node:
                        all_var_node[var] = self.var_node[var]
                    else:
                        if all_var_node[var].line < self.var_node[var].line:
                            all_var_node[var] = self.var_node[var]
                self.var_node = {k:v for k,v in original_var_node.items()}
                self.push_type_map(else_map, else_node, false_literal)
            with self.binder.frame_context(can_skip=False, fall_through=2):
                if s.else_body:
                    self.accept(s.else_body)
            for var in self.var_node:
                if var not in all_var_node:
                    all_var_node[var] = self.var_node[var]
                else:
                    if all_var_node[var].line < self.var_node[var].line:
                        all_var_node[var] = self.var_node[var]
            self.var_node = {k:v for k,v in all_var_node.items()}
    def visit_while_stmt(self, s: WhileStmt) -> None:
        if_stmt = IfStmt([s.expr], [s.body], None)
        if_stmt.set_line(s.get_line(), s.get_column())
        self.accept_loop(if_stmt, s.else_body,
                         exit_condition=s.expr)
    def visit_operator_assignment_stmt(self,
                                       s: OperatorAssignmentStmt) -> None:
        if isinstance(s.lvalue, MemberExpr):
            lvalue_type = self.expr_checker.visit_member_expr(s.lvalue, True)
        else:
            lvalue_type = self.expr_checker.accept(s.lvalue)
        inplace, method = infer_operator_assignment_method(lvalue_type, s.op)
        method_node = TempNode(method, s)
        return_node = TempNode(AnyType(0), s)
        if inplace:
            rvalue_type, method_type = self.expr_checker.check_op(
                method, lvalue_type, s.rvalue, s, object_node = s.lvalue, method_node=method_node, return_node=return_node)
        else:
            temp_left = TempNode(lvalue_type, context = s.lvalue)
            expr = OpExpr(s.op, s.lvalue, s.rvalue)
            expr.set_line(s)
            self.check_assignment(lvalue=s.lvalue, rvalue=expr,
                                  infer_lvalue_type=True, new_syntax=False)
    def visit_assert_stmt(self, s: AssertStmt) -> None:
        self.expr_checker.accept(s.expr)
        true_map, else_map = self.find_isinstance_check(s.expr)
        if s.msg is not None:
            self.expr_checker.analyze_cond_branch(else_map, s.msg, None)
        self.push_type_map(true_map)
    def visit_raise_stmt(self, s: RaiseStmt) -> None:
        self.binder.unreachable()
    def visit_try_stmt(self, s: TryStmt) -> None:
        with self.binder.frame_context(can_skip=False, fall_through=0):
            self.visit_try_without_finally(s, try_frame=bool(s.finally_body))
            if s.finally_body:
                self.accept(s.finally_body)
        if s.finally_body:
            if not self.binder.is_unreachable():
                self.accept(s.finally_body)
    def visit_try_without_finally(self, s: TryStmt, try_frame: bool) -> None:
        with self.binder.frame_context(can_skip=False, fall_through=2, try_frame=try_frame):
            with self.binder.frame_context(can_skip=False, conditional_frame=True, fall_through=2):
                with self.binder.frame_context(can_skip=False, fall_through=2, try_frame=True):
                    self.accept(s.body)
                for i in range(len(s.handlers)):
                    with self.binder.frame_context(can_skip=True, fall_through=4):
                        typ = s.types[i]
                        if typ:
                            var = s.vars[i]
                            if var:
                                var.is_inferred_def = True
                                am_deferring = self.current_node_deferred
                                self.current_node_deferred = False
                                self.current_node_deferred = am_deferring
                        self.accept(s.handlers[i])
                        var = s.vars[i]
                        if var:
                            if self.options.python_version[0] >= 3:
                                source = var.name
                            else:
                                source = ('(exception variable "{}", which we do not '
                                          'accept outside except: blocks even in '
                                          'python 2)'.format(var.name))
                            if isinstance(var.node, Var):
                                var.node.type = DeletedType(source=source)
                            self.binder.cleanse(var)
            if s.else_body:
                self.accept(s.else_body)
    def visit_for_stmt(self, s: ForStmt) -> None:
        iterator_type, item_type, ret_node = self.analyze_iterable_item_type(s.expr)
        s.inferred_item_type = item_type
        s.inferred_iterator_type = iterator_type
        self.analyze_index_variables(s.index, item_type, s.index_type is None, s, ret_node)
        self.accept_loop(s.body, s.else_body)
    def analyze_iterable_item_type(self, expr: Expression) -> Tuple[Type, Set[Type]]:
        echk = self.expr_checker
        iterable = echk.accept(expr)
        expr.set_depth(1)
        method_node = TempNode(AnyType(0), context=expr)
        return_node = TempNode(AnyType(0), context=expr)
        iterator = echk.check_method_call_by_name('__iter__', iterable, [], [], expr, object_node=expr, method_node=method_node, return_node=return_node)[0]
        if isinstance(iterable, TupleType):
            joined: Type = UninhabitedType()
            for item in iterable.items:
                joined = join_types(joined, item)
            return iterator, joined, return_node
        else:
            if self.options.python_version[0] >= 3:
                nextmethod = '__next__'
            else:
                nextmethod = 'next'
            method_node2 = TempNode(AnyType(0), context=return_node)
            return_node2 = TempNode(AnyType(0), context=return_node)
            return iterator, echk.check_method_call_by_name(nextmethod, iterator, [], [], expr, object_node=return_node, method_node=method_node2, return_node=return_node2)[0], return_node2
    def analyze_container_item_type(self, typ: Type) -> Optional[Type]:
        """Check if a type is a nominal container of a union of such.
        Return the corresponding container item type.
        """
        if isinstance(typ, UnionType):
            types: List[Type] = []
            for item in typ.items:
                c_type = self.analyze_container_item_type(item)
                if c_type:
                    types.append(c_type)
            return UnionType.make_union(types)
        if isinstance(typ, Instance) and typ.type.has_base('typing.Container'):
            supertype = self.named_type('typing.Container').type
            super_instance = map_instance_to_supertype(typ, supertype)
            assert len(super_instance.args) == 1
            return super_instance.args[0]
        if isinstance(typ, TupleType):
            return self.analyze_container_item_type(tuple_fallback(typ))
        return None
    def analyze_index_variables(self, index: Expression, item_type: Set[Type],
                                infer_lvalue_type: bool, context: Context, ret_node=None) -> None:
        if ret_node is None:
            self.check_assignment(index, self.temp_node(item_type, context), infer_lvalue_type)
        else:
            self.check_assignment(index, ret_node, infer_lvalue_type)
    def visit_del_stmt(self, s: DelStmt) -> None:
        if isinstance(s.expr, IndexExpr):
            e = s.expr
            m = MemberExpr(e.base, '__delitem__')
            m.line = s.line
            m.column = s.column
            c = CallExpr(m, [e.index], [nodes.ARG_POS], [None])
            c.line = s.line
            c.column = s.column
            self.expr_checker.accept(c)
        else:
            s.expr.accept(self.expr_checker)
            for elt in flatten(s.expr):
                if isinstance(elt, NameExpr):
                    self.binder.assign_type(elt, DeletedType(source=elt.name),
                                            get_declaration(elt), False)
    def visit_decorator(self, e: Decorator) -> None:
        for d in e.decorators:
            if isinstance(d, RefExpr):
                if d.fullname == 'typing.no_type_check':
                    e.var.type = AnyType(TypeOfAny.special_form)
                    e.var.is_ready = True
                    return
        if self.recurse_into_functions:
            with self.tscope.function_scope(e.func):
                self.check_func_item(e.func)
    def visit_with_stmt(self, s: WithStmt) -> None:
        exceptions_maybe_suppressed = False
        for expr, target in zip(s.expr, s.target):
            exit_ret_type = self.check_with_item(expr, target, s.unanalyzed_type is None)   
        if exceptions_maybe_suppressed:
            with self.binder.frame_context(can_skip=True, try_frame=True):
                self.accept(s.body)
        else:
            self.accept(s.body)
    def check_with_item(self, expr: Expression, target: Optional[Expression],
                        infer_lvalue_type: bool) -> Set[Type]:
        echk = self.expr_checker
        ctx = echk.accept(expr)
        method_node = TempNode(AnyType(101), context=expr)
        return_node = TempNode(AnyType(101), context=expr)
        obj = echk.check_method_call_by_name('__enter__', ctx, [], [], expr, object_node=expr, method_node=method_node, return_node=return_node)[0]
        if target:
            self.check_assignment(target, return_node, infer_lvalue_type)
        arg = self.temp_node(AnyType(TypeOfAny.special_form), expr)
        self.store_type(arg, [AnyType(TypeOfAny.special_form)]) 
        method_node = TempNode(AnyType(102), context=expr)
        return_node = TempNode(AnyType(102), context=expr)
        res, _ = echk.check_method_call_by_name(
            '__exit__', ctx, [arg] * 3, [nodes.ARG_POS] * 3, expr, object_node=expr, method_node=method_node, return_node=return_node)
        return res
    def visit_print_stmt(self, s: PrintStmt) -> None:
        for arg in s.args:
            self.expr_checker.accept(arg)
        if s.target:
            target_type = self.expr_checker.accept(s.target)
    def visit_break_stmt(self, s: BreakStmt) -> None:
        self.binder.handle_break()
    def visit_continue_stmt(self, s: ContinueStmt) -> None:
        self.binder.handle_continue()
        return None
    def make_fake_typeinfo(self,
                           curr_module_fullname: str,
                           class_gen_name: str,
                           class_short_name: str,
                           bases: List[Instance],
                           ) -> Tuple[ClassDef, TypeInfo]:
        cdef = ClassDef(class_short_name, Block([]))
        cdef.fullname = curr_module_fullname + '.' + class_gen_name
        info = TypeInfo(SymbolTable(), cdef, curr_module_fullname)
        cdef.info = info
        info.bases = bases
        calculate_mro(info)
        info.calculate_metaclass_type()
        return cdef, info
    def intersect_instances(self,
                            instances: Tuple[Instance, Instance],
                            ctx: Context,
                            ) -> Optional[Instance]:
        """Try creating an ad-hoc intersection of the given instances.
        Note that this function does *not* try and create a full-fledged
        intersection type. Instead, it returns an instance of a new ad-hoc
        subclass of the given instances.
        This is mainly useful when you need a way of representing some
        theoretical subclass of the instances the user may be trying to use
        the generated intersection can serve as a placeholder.
        This function will create a fresh subclass every time you call it,
        even if you pass in the exact same arguments. So this means calling
        `self.intersect_intersection([inst_1, inst_2], ctx)` twice will result
        in instances of two distinct subclasses of inst_1 and inst_2.
        This is by design: we want each ad-hoc intersection to be unique since
        they're supposed represent some other unknown subclass.
        Returns None if creating the subclass is impossible (e.g. due to
        MRO errors or incompatible signatures). If we do successfully create
        a subclass, its TypeInfo will automatically be added to the global scope.
        """
        curr_module = self.scope.stack[0]
        assert isinstance(curr_module, MypyFile)
        def _get_base_classes(instances_: Tuple[Instance, Instance]) -> List[Instance]:
            base_classes_ = []
            for inst in instances_:
                expanded = [inst]
                if inst.type.is_intersection:
                    expanded = inst.type.bases
                for expanded_inst in expanded:
                    base_classes_.append(expanded_inst)
            return base_classes_
        def _make_fake_typeinfo_and_full_name(
                base_classes_: List[Instance],
                curr_module_: MypyFile,
        ) -> Tuple[TypeInfo, str]:
            names_list = pretty_seq([x.type.name for x in base_classes_], "and")
            short_name = '<subclass of {}>'.format(names_list)
            full_name_ = gen_unique_name(short_name, curr_module_.names)
            cdef, info_ = self.make_fake_typeinfo(
                curr_module_.fullname,
                full_name_,
                short_name,
                base_classes_,
            )
            return info_, full_name_
        old_msg = self.msg
        new_msg = old_msg.clean_copy()
        self.msg = new_msg
        base_classes = _get_base_classes(instances)
        pretty_names_list = pretty_seq(format_type_distinctly(*base_classes, bare=True), "and")
        try:
            info, full_name = _make_fake_typeinfo_and_full_name(base_classes, curr_module)
            self.check_multiple_inheritance(info)
            if new_msg.is_errors():
                new_msg = new_msg.clean_copy()
                self.msg = new_msg
                base_classes = _get_base_classes(instances[::-1])
                info, full_name = _make_fake_typeinfo_and_full_name(base_classes, curr_module)
                self.check_multiple_inheritance(info)
            info.is_intersection = True
        except MroError:
            return None
        finally:
            self.msg = old_msg
        if new_msg.is_errors():
            return None
        curr_module.names[full_name] = SymbolTableNode(GDEF, info)
        return Instance(info, [])
    def intersect_instance_callable(self, typ: Instance, callable_type: CallableType) -> Instance:
        """Creates a fake type that represents the intersection of an Instance and a CallableType.
        It operates by creating a bare-minimum dummy TypeInfo that
        subclasses type and adds a __call__ method matching callable_type.
        """
        cur_module = cast(MypyFile, self.scope.stack[0])
        gen_name = gen_unique_name("<callable subtype of {}>".format(typ.type.name),
                                   cur_module.names)
        short_name = format_type_bare(typ)
        cdef, info = self.make_fake_typeinfo(cur_module.fullname, gen_name, short_name, [typ])
        func_def = FuncDef('__call__', [], Block([]), callable_type)
        func_def._fullname = cdef.fullname + '.__call__'
        func_def.info = info
        info.names['__call__'] = SymbolTableNode(MDEF, func_def)
        cur_module.names[gen_name] = SymbolTableNode(GDEF, info)
        return Instance(info, [])
    def make_fake_callable(self, typ: Instance) -> Instance:
        fallback = self.named_type('builtins.function')
        callable_type = CallableType([AnyType(TypeOfAny.explicit),
                                      AnyType(TypeOfAny.explicit)],
                                     [nodes.ARG_STAR, nodes.ARG_STAR2],
                                     [None, None],
                                     ret_type=AnyType(TypeOfAny.explicit),
                                     fallback=fallback,
                                     is_ellipsis_args=True)
        return self.intersect_instance_callable(typ, callable_type)
    def partition_by_callable(self, typ: Type,
                              unsound_partition: bool) -> Tuple[List[Type], List[Type]]:
        """Partitions a type into callable subtypes and uncallable subtypes.
        Thus, given:
        `callables, uncallables = partition_by_callable(type)`
        If we assert `callable(type)` then `type` has type Union[*callables], and
        If we assert `not callable(type)` then `type` has type Union[*uncallables]
        If unsound_partition is set, assume that anything that is not
        clearly callable is in fact not callable. Otherwise we generate a
        new subtype that *is* callable.
        Guaranteed to not return [], [].
        """
        typ = get_proper_type(typ)
        if isinstance(typ, FunctionLike) or isinstance(typ, TypeType):
            return [typ], []
        if isinstance(typ, AnyType):
            return [typ], [typ]
        if isinstance(typ, NoneType):
            return [], [typ]
        if isinstance(typ, UnionType):
            callables = []
            uncallables = []
            for subtype in typ.items:
                subcallables, subuncallables = self.partition_by_callable(subtype,
                                                                          unsound_partition=True)
                callables.extend(subcallables)
                uncallables.extend(subuncallables)
            return callables, uncallables
        if isinstance(typ, TypeVarType):
            callables, uncallables = self.partition_by_callable(erase_to_union_or_bound(typ),
                                                                unsound_partition)
            uncallables = [typ] if len(uncallables) else []
            return callables, uncallables
        ityp = typ
        if isinstance(typ, TupleType):
            ityp = tuple_fallback(typ)
        if isinstance(ityp, Instance):
            method = ityp.type.get_method('__call__')
            if method and method.type:
                callables, uncallables = self.partition_by_callable(method.type,
                                                                    unsound_partition=False)
                if len(callables) and not len(uncallables):
                    return [typ], []
            if not unsound_partition:
                fake = self.make_fake_callable(ityp)
                if isinstance(typ, TupleType):
                    fake.type.tuple_type = TupleType(typ.items, fake)
                    return [fake.type.tuple_type], [typ]
                return [fake], [typ]
        if unsound_partition:
            return [], [typ]
        else:
            return [typ], [typ]
    def conditional_callable_type_map(self, expr: Expression,
                                      current_type: Optional[Type],
                                      ) -> Tuple[TypeMap, TypeMap]:
        """Takes in an expression and the current type of the expression.
        Returns a 2-tuple: The first element is a map from the expression to
        the restricted type if it were callable. The second element is a
        map from the expression to the type it would hold if it weren't
        callable.
        """
        if not current_type:
            return {}, {}
        if isinstance(get_proper_type(current_type), AnyType):
            return {}, {}
        callables, uncallables = self.partition_by_callable(current_type,
                                                            unsound_partition=False)
        if len(callables) and len(uncallables):
            callable_map = {expr: UnionType.make_union(callables)} if len(callables) else None
            uncallable_map = {
                expr: UnionType.make_union(uncallables)} if len(uncallables) else None
            return callable_map, uncallable_map
        elif len(callables):
            return {}, None
        return None, {}
    def find_type_equals_check(self, node: ComparisonExpr, expr_indices: List[int]
                               ) -> Tuple[TypeMap, TypeMap]:
        """Narrow types based on any checks of the type ``type(x) == T``
        Args:
            node: The node that might contain the comparison
            expr_indices: The list of indices of expressions in ``node`` that are being
                compared
        """
        type_map = self.type_map
        def is_type_call(expr: CallExpr) -> bool:
            return (refers_to_fullname(expr.callee, 'builtins.type')
                    and len(expr.args) == 1)
        exprs_in_type_calls: List[Expression] = []
        type_being_compared: Optional[List[TypeRange]] = None
        is_final = False
        for index in expr_indices:
            expr = node.operands[index]
            if isinstance(expr, CallExpr) and is_type_call(expr):
                exprs_in_type_calls.append(expr.args[0])
            else:
                current_type = get_isinstance_type(expr, type_map)
                if current_type is None:
                    continue
                if type_being_compared is not None:
                    return {}, {}
                else:
                    if isinstance(expr, RefExpr) and isinstance(expr.node, TypeInfo):
                        is_final = expr.node.is_final
                    type_being_compared = current_type
        if not exprs_in_type_calls:
            return {}, {}
        if_maps: List[TypeMap] = []
        else_maps: List[TypeMap] = []
        for expr in exprs_in_type_calls:
            current_if_map, current_else_map = self.conditional_type_map_with_intersection(
                expr,
                type_map[expr],
                type_being_compared
            )
            if_maps.append(current_if_map)
            else_maps.append(current_else_map)
        def combine_maps(list_maps: List[TypeMap]) -> TypeMap:
            result_map = {}
            for d in list_maps:
                if d is not None:
                    result_map.update(d)
            return result_map
        if_map = combine_maps(if_maps)
        if is_final:
            else_map = combine_maps(else_maps)
        else:
            else_map = {}
        return if_map, else_map
    def find_isinstance_check(self, node: Expression
                              ) -> Tuple[TypeMap, TypeMap]:
        if_map, else_map = self.find_isinstance_check_helper(node)
        new_if_map = self.propagate_up_typemap_info(self.type_map, if_map)
        new_else_map = self.propagate_up_typemap_info(self.type_map, else_map)
        return new_if_map, new_else_map
    def find_isinstance_check_helper(self, node: Expression) -> Tuple[TypeMap, TypeMap]:
        """
        Some narrowing are not supported by Stray now. However, we keep the original narrowing logic of mypy. 
        Hopefully, we will found some time to support them referring the logic of mypy. 
        """
        type_map = self.type_map
        if is_true_literal(node):
            return {}, None
        elif is_false_literal(node):
            return None, {}
        elif isinstance(node, CallExpr):
            if len(node.args) == 0:
                return {}, {}
            expr = collapse_walrus(node.args[0])
            if refers_to_fullname(node.callee, 'builtins.isinstance'):
                if len(node.args) != 2:  
                    return {}, {}
                if literal(expr) == LITERAL_TYPE:
                    return self.conditional_type_map_with_intersection(
                        expr,
                        type_map[expr],
                        get_isinstance_type(node.args[1], type_map),
                    )
            elif refers_to_fullname(node.callee, 'builtins.issubclass'):
                return {}, {}
            elif refers_to_fullname(node.callee, 'builtins.callable'):
                return {}, {}
            elif isinstance(node.callee, RefExpr):
                return {}, {}
        elif isinstance(node, ComparisonExpr):
            return {}, {}
        elif isinstance(node, AssignmentExpr):
            return self.find_isinstance_check_helper(node.target)
        elif isinstance(node, RefExpr):
            var_types = type_map[node] 
            if_hook = defaultdict(list)
            else_hook = defaultdict(list)
            if_types = []
            else_types = []
            for vartype in var_types:
                if_type: Type = true_only(vartype)
                else_type: Type = false_only(vartype)
                ref: Expression = node
                if_types.append(if_type)
                else_types.append(else_type)
            if_map = {ref: if_types}
            else_map = {ref: else_types}
            return if_map, else_map
        elif isinstance(node, OpExpr) and node.op == 'and':
            left_if_vars, left_else_vars = self.find_isinstance_check_helper(node.left)
            right_if_vars, right_else_vars = self.find_isinstance_check_helper(node.right)
            return (and_conditional_maps(left_if_vars, right_if_vars),
                    or_conditional_maps(left_else_vars, right_else_vars))
        elif isinstance(node, OpExpr) and node.op == 'or':
            left_if_vars, left_else_vars = self.find_isinstance_check_helper(node.left)
            right_if_vars, right_else_vars = self.find_isinstance_check_helper(node.right)
            return (or_conditional_maps(left_if_vars, right_if_vars),
                    and_conditional_maps(left_else_vars, right_else_vars))
        elif isinstance(node, UnaryExpr) and node.op == 'not':
            left, right = self.find_isinstance_check_helper(node.expr)
            return right, left
        return {}, {}
    def propagate_up_typemap_info(self,
                                  existing_types: Mapping[Expression, Type],
                                  new_types: TypeMap) -> TypeMap:
        """Attempts refining parent expressions of any MemberExpr or IndexExprs in new_types.
        Specifically, this function accepts two mappings of expression to original types:
        the original mapping (existing_types), and a new mapping (new_types) intended to
        update the original.
        This function iterates through new_types and attempts to use the information to try
        refining any parent types that happen to be unions.
        For example, suppose there are two types "A = Tuple[int, int]" and "B = Tuple[str, str]".
        Next, suppose that 'new_types' specifies the expression 'foo[0]' has a refined type
        of 'int' and that 'foo' was previously deduced to be of type Union[A, B].
        Then, this function will observe that since A[0] is an int and B[0] is not, the type of
        'foo' can be further refined from Union[A, B] into just B.
        We perform this kind of "parent narrowing" for member lookup expressions and indexing
        expressions into tuples, namedtuples, and typeddicts. We repeat this narrowing
        recursively if the parent is also a "lookup expression". So for example, if we have
        the expression "foo['bar'].baz[0]", we'd potentially end up refining types for the
        expressions "foo", "foo['bar']", and "foo['bar'].baz".
        We return the newly refined map. This map is guaranteed to be a superset of 'new_types'.
        """
        if new_types is None:
            return None
        output_map = {}
        for expr, expr_type in new_types.items():
            output_map[expr] = expr_type
            new_mapping = self.refine_parent_types(existing_types, expr, expr_type)
            for parent_expr, proposed_parent_type in new_mapping.items():
                if parent_expr in new_types:
                    continue
                output_map[parent_expr] = proposed_parent_type
        return output_map
    def refine_parent_types(self,
                            existing_types: Mapping[Expression, Type],
                            expr: Expression,
                            expr_type: Type) -> Mapping[Expression, Type]:
        """Checks if the given expr is a 'lookup operation' into a union and iteratively refines
        the parent types based on the 'expr_type'.
        For example, if 'expr' is an expression like 'a.b.c.d', we'll potentially return refined
        types for expressions 'a', 'a.b', and 'a.b.c'.
        For more details about what a 'lookup operation' is and how we use the expr_type to refine
        the parent types of lookup_expr, see the docstring in 'propagate_up_typemap_info'.
        """
        output: Dict[Expression, Type] = {}
        while True:
            if isinstance(expr, MemberExpr):
                parent_expr = expr.expr
                parent_type = existing_types.get(parent_expr)
                member_name = expr.name
                def replay_lookup(new_parent_type: ProperType) -> Optional[Type]:
                    msg_copy = self.msg.clean_copy()
                    msg_copy.disable_count = 0
                    member_type = analyze_member_access(
                        name=member_name,
                        typ=new_parent_type,
                        context=parent_expr,
                        is_lvalue=False,
                        is_super=False,
                        is_operator=False,
                        msg=msg_copy,
                        original_type=new_parent_type,
                        chk=self,
                        in_literal_context=False,
                    )
                    if msg_copy.is_errors():
                        return None
                    else:
                        return member_type
            elif isinstance(expr, IndexExpr):
                parent_expr = expr.base
                parent_type = existing_types.get(parent_expr)
                index_type = existing_types.get(expr.index)
                if index_type is None:
                    return output
                str_literals = try_getting_str_literals_from_type(index_type)
                if str_literals is not None:
                    def replay_lookup(new_parent_type: ProperType) -> Optional[Type]:
                        if not isinstance(new_parent_type, TypedDictType):
                            return None
                        try:
                            assert str_literals is not None
                            member_types = [new_parent_type.items[key] for key in str_literals]
                        except KeyError:
                            return None
                        return make_simplified_union(member_types)
                else:
                    int_literals = try_getting_int_literals_from_type(index_type)
                    if int_literals is not None:
                        def replay_lookup(new_parent_type: ProperType) -> Optional[Type]:
                            if not isinstance(new_parent_type, TupleType):
                                return None
                            try:
                                assert int_literals is not None
                                member_types = [new_parent_type.items[key] for key in int_literals]
                            except IndexError:
                                return None
                            return make_simplified_union(member_types)
                    else:
                        return output
            else:
                return output
            if parent_type is None:
                return output
            parent_type = get_proper_type(parent_type)
            if not isinstance(parent_type, UnionType):
                return output
            new_parent_types = []
            for item in parent_type.items:
                item = get_proper_type(item)
                member_type = replay_lookup(item)
                if member_type is None:
                    return output
                if is_overlapping_types(member_type, expr_type):
                    new_parent_types.append(item)
            if not new_parent_types:
                return output
            expr = parent_expr
            expr_type = output[parent_expr] = make_simplified_union(new_parent_types)
        return output
    def refine_identity_comparison_expression(self,
                                              operands: List[Expression],
                                              operand_types: List[Type],
                                              chain_indices: List[int],
                                              narrowable_operand_indices: AbstractSet[int],
                                              is_valid_target: Callable[[ProperType], bool],
                                              coerce_only_in_literal_context: bool,
                                              ) -> Tuple[TypeMap, TypeMap]:
        """Produce conditional type maps refining expressions by an identity/equality comparison.
        The 'operands' and 'operand_types' lists should be the full list of operands used
        in the overall comparison expression. The 'chain_indices' list is the list of indices
        actually used within this identity comparison chain.
        So if we have the expression:
            a <= b is c is d <= e
        ...then 'operands' and 'operand_types' would be lists of length 5 and 'chain_indices'
        would be the list [1, 2, 3].
        The 'narrowable_operand_indices' parameter is the set of all indices we are allowed
        to refine the types of: that is, all operands that will potentially be a part of
        the output TypeMaps.
        Although this function could theoretically try setting the types of the operands
        in the chains to the meet, doing that causes too many issues in real-world code.
        Instead, we use 'is_valid_target' to identify which of the given chain types
        we could plausibly use as the refined type for the expressions in the chain.
        Similarly, 'coerce_only_in_literal_context' controls whether we should try coercing
        expressions in the chain to a Literal type. Performing this coercion is sometimes
        too aggressive of a narrowing, depending on context.
        """
        should_coerce = True
        if coerce_only_in_literal_context:
            should_coerce = any(is_literal_type_like(operand_types[i]) for i in chain_indices)
        target: Optional[Type] = None
        possible_target_indices = []
        for i in chain_indices:
            expr_type = operand_types[i]
            if should_coerce:
                expr_type = coerce_to_literal(expr_type)
            if not is_valid_target(get_proper_type(expr_type)):
                continue
            if target and not is_same_type(target, expr_type):
                return None, {}
            target = expr_type
            possible_target_indices.append(i)
        if target is None:
            return {}, {}
        singleton_index = -1
        for i in possible_target_indices:
            if i not in narrowable_operand_indices:
                singleton_index = i
        if singleton_index == -1:
            singleton_index = possible_target_indices[-1]
        enum_name = None
        target = get_proper_type(target)
        if isinstance(target, LiteralType) and target.is_enum_literal():
            enum_name = target.fallback.type.fullname
        target_type = [TypeRange(target, is_upper_bound=False)]
        partial_type_maps = []
        for i in chain_indices:
            if i == singleton_index:
                continue
            if i not in narrowable_operand_indices:
                continue
            expr = operands[i]
            expr_type = coerce_to_literal(operand_types[i])
            if enum_name is not None:
                expr_type = try_expanding_enum_to_union(expr_type, enum_name)
            partial_type_maps.append(conditional_type_map(expr, expr_type, target_type))
        return reduce_conditional_maps(partial_type_maps)
    def refine_away_none_in_comparison(self,
                                       operands: List[Expression],
                                       operand_types: List[Type],
                                       chain_indices: List[int],
                                       narrowable_operand_indices: AbstractSet[int],
                                       ) -> Tuple[TypeMap, TypeMap]:
        """Produces conditional type maps refining away None in an identity/equality chain.
        For more details about what the different arguments mean, see the
        docstring of 'refine_identity_comparison_expression' up above.
        """
        non_optional_types = []
        for i in chain_indices:
            typ = operand_types[i]
            if not is_optional(typ):
                non_optional_types.append(typ)
        if len(non_optional_types) == 0 or len(non_optional_types) == len(chain_indices):
            return {}, {}
        if_map = {}
        for i in narrowable_operand_indices:
            expr_type = operand_types[i]
            if not is_optional(expr_type):
                continue
            if any(is_overlapping_erased_types(expr_type, t) for t in non_optional_types):
                if_map[operands[i]] = remove_optional(expr_type)
        return if_map, {}
    def check_subtype(self,
                      subtype: Type,
                      supertype: Type,
                      context: Context,
                      msg: str = message_registry.INCOMPATIBLE_TYPES,
                      subtype_label: Optional[str] = None,
                      supertype_label: Optional[str] = None,
                      *,
                      code: Optional[ErrorCode] = None,
                      outer_context: Optional[Context] = None) -> bool:
        if isinstance(subtype, (set, list)) or isinstance(supertype, (set, list)):
            return True
        if is_subtype(subtype, supertype):
            return True
        self.err_cnts += 1
        subtype = get_proper_type(subtype)
        supertype = get_proper_type(supertype)
        if self.msg.try_report_long_tuple_assignment_error(subtype, supertype, context, msg,
                                       subtype_label, supertype_label, code=code):
            return False
        if self.should_suppress_optional_error([subtype]):
            return False
        extra_info: List[str] = []
        note_msg = ''
        notes: List[str] = []
        if subtype_label is not None or supertype_label is not None:
            subtype_str, supertype_str = format_type_distinctly(subtype, supertype)
            if subtype_label is not None:
                extra_info.append(subtype_label + ' ' + subtype_str)
            if supertype_label is not None:
                extra_info.append(supertype_label + ' ' + supertype_str)
            note_msg = make_inferred_type_note(outer_context or context, subtype,
                                               supertype, supertype_str)
            if isinstance(subtype, Instance) and isinstance(supertype, Instance):
                notes = append_invariance_notes([], subtype, supertype)
        if extra_info:
            msg += ' (' + ', '.join(extra_info) + ')'
        self.fail(msg, context, code=code)
        for note in notes:
            self.msg.note(note, context, code=code)
        if note_msg:
            self.note(note_msg, context, code=code)
        if (isinstance(supertype, Instance) and supertype.type.is_protocol and
                isinstance(subtype, (Instance, TupleType, TypedDictType))):
            self.msg.report_protocol_problems(subtype, supertype, context, code=code)
        if isinstance(supertype, CallableType) and isinstance(subtype, Instance):
            call = find_member('__call__', subtype, subtype, is_operator=True)
            if call:
                self.msg.note_call(subtype, call, context, code=code)
        if isinstance(subtype, (CallableType, Overloaded)) and isinstance(supertype, Instance):
            if supertype.type.is_protocol and supertype.type.protocol_members == ['__call__']:
                call = find_member('__call__', supertype, subtype, is_operator=True)
                assert call is not None
                self.msg.note_call(supertype, call, context, code=code)
        return False
    def contains_none(self, t: Type) -> bool:
        t = get_proper_type(t)
        return (
            isinstance(t, NoneType) or
            (isinstance(t, UnionType) and any(self.contains_none(ut) for ut in t.items)) or
            (isinstance(t, TupleType) and any(self.contains_none(tt) for tt in t.items)) or
            (isinstance(t, Instance) and bool(t.args)
             and any(self.contains_none(it) for it in t.args))
        )
    def should_suppress_optional_error(self, related_types: List[Type]) -> bool:
        return self.suppress_none_errors and any(self.contains_none(t) for t in related_types)
    def named_dict_with_type_var(self, name: str, tk, tv):
        sym = self.lookup_qualified(name)
        node = sym.node
        if isinstance(node, TypeAlias):
            assert isinstance(node.target, Instance)  
            node = node.target.type
        assert isinstance(node, TypeInfo)
        return Instance(node, [tk, tv])
    def named_type_with_type_var(self, name: str, tv):
        sym = self.lookup_qualified(name)
        node = sym.node
        if isinstance(node, TypeAlias):
            assert isinstance(node.target, Instance)  
            node = node.target.type
        assert isinstance(node, TypeInfo)
        return Instance(node, [tv] * len(node.defn.type_vars))
    def named_type(self, name: str) -> Instance:
        """Return an instance type with given name and implicit Any type args.
        For example, named_type('builtins.object') produces the 'object' type.
        """
        sym = self.lookup_qualified(name)
        node = sym.node
        if isinstance(node, TypeAlias):
            assert isinstance(node.target, Instance)  
            node = node.target.type
        if isinstance(node, TypeInfo):
            any_type = AnyType(TypeOfAny.from_omitted_generics)
            return Instance(node, [any_type] * len(node.defn.type_vars))
    def named_type_optional(self, name: str) -> Instance:
        """Return an instance type with given name and implicit Any type args.
        For example, named_type('builtins.object') produces the 'object' type.
        """
        sym = self.lookup_qualified(name)
        node = sym.node
        if isinstance(node, TypeAlias):
            assert isinstance(node.target, Instance)  
            node = node.target.type
        assert isinstance(node, TypeInfo)
        any_type = AnyType(TypeOfAny.from_omitted_generics)
        return make_optional_type(Instance(node, [any_type] * len(node.defn.type_vars)))
    def named_generic_type(self, name: str, args: List[Type]) -> Instance:
        """Return an instance with the given name and type arguments.
        Assume that the number of arguments is correct.  Assume that
        the name refers to a compatible generic type.
        """
        args = [next(iter(arg)) if isinstance(arg, (list,set)) else arg for arg in args]
        info = self.lookup_typeinfo(name)
        args = [remove_instance_last_known_values(arg) for arg in args]
        return Instance(info, args)
    def lookup_typeinfo(self, fullname: str) -> TypeInfo:
        sym = self.lookup_qualified(fullname)
        node = sym.node
        assert isinstance(node, TypeInfo)
        return node
    def type_type(self) -> Instance:
        return self.named_type('builtins.type')
    def str_type(self) -> Instance:
        return self.named_type('builtins.str')
    def store_type(self, node: Expression,  typ: Set[Type], overwrite=True, state=None) -> None:
        if not (isinstance(typ, list) or isinstance(typ, set)):
            typ = [typ]
        typ = set(typ)
        if state:
            state.type_map[node] = typ
            return
        if not overwrite and node in self.wide_type_map:
            self.wide_type_map[node].update(typ)
            self.type_map[node].update(typ)
        self.wide_type_map[node] = typ
        self.type_map[node] = typ
    def lookup(self, name: str, kind: int) -> SymbolTableNode:
        """Look up a definition from the symbol table with the given name.
        TODO remove kind argument
        """
        if name in self.globals:
            return self.globals[name]
        else:
            b = self.globals.get('__builtins__', None)
            if b:
                table = cast(MypyFile, b.node).names
                if name in table:
                    return table[name]
            raise KeyError('Failed lookup: {}'.format(name))
    def lookup_qualified(self, name: str) -> SymbolTableNode:
        if '.' not in name:
            return self.lookup(name, GDEF)  
        else:
            parts = name.split('.')
            n = self.modules[parts[0]]
            for i in range(1, len(parts) - 1):
                sym = n.names.get(parts[i])
                assert sym is not None, "Internal error: attempted lookup of unknown name"
                n = cast(MypyFile, sym.node)
            last = parts[-1]
            if last in n.names:
                return n.names[last]
            elif len(parts) == 2 and parts[0] == 'builtins':
                fullname = 'builtins.' + last
                if fullname in SUGGESTED_TEST_FIXTURES:
                    suggestion = ", e.g. add '[builtins fixtures/{}]' to your test".format(
                        SUGGESTED_TEST_FIXTURES[fullname])
                else:
                    suggestion = ''
                raise KeyError("Could not find builtin symbol '{}' (If you are running a "
                               "test case, use a fixture that "
                               "defines this symbol{})".format(last, suggestion))
            else:
                msg = "Failed qualified lookup: '{}' (fullname = '{}')."
                raise KeyError(msg.format(last, name))
    def fixup_partial_type(self, typ: Type) -> Type:
        """Convert a partial type that we couldn't resolve into something concrete.
        This means, for None we make it Optional[Any], and for anything else we
        fill in all of the type arguments with Any.
        """
        if not isinstance(typ, PartialType):
            return typ
        if typ.type is None:
            return UnionType.make_union([AnyType(TypeOfAny.unannotated), NoneType()])
        else:
            return Instance(
                typ.type,
                [AnyType(TypeOfAny.unannotated)] * len(typ.type.type_vars))
    def is_defined_in_base_class(self, var: Var) -> bool:
        if var.info:
            for base in var.info.mro[1:]:
                if base.get(var.name) is not None:
                    return True
            if var.info.fallback_to_any:
                return True
        return False
    def find_partial_types(self, var: Var) -> Optional[Dict[Var, Context]]:
        """Look for an active partial type scope containing variable.
        A scope is active if assignments in the current context can refine a partial
        type originally defined in the scope. This is affected by the local_partial_types
        configuration option.
        """
        in_scope, _, partial_types = self.find_partial_types_in_all_scopes(var)
        if in_scope:
            return partial_types
        return None
    def find_partial_types_in_all_scopes(
            self, var: Var) -> Tuple[bool, bool, Optional[Dict[Var, Context]]]:
        """Look for partial type scope containing variable.
        Return tuple (is the scope active, is the scope a local scope, scope).
        """
        for scope in reversed(self.partial_types):
            if var in scope.map:
                disallow_other_scopes = self.options.local_partial_types
                if isinstance(var.type, PartialType) and var.type.type is not None and var.info:
                    disallow_other_scopes = True
                scope_active = (not disallow_other_scopes
                                or scope.is_local == self.partial_types[-1].is_local)
                return scope_active, scope.is_local, scope.map
        return False, False, None
    def temp_node(self, t: Type, context: Optional[Context] = None) -> TempNode:
        return TempNode(t, context=context)
    def fail(self, msg: str, context: Context, *, code: Optional[ErrorCode] = None) -> None:
        self.msg.fail(msg, context, code=code)
    def note(self,
             msg: str,
             context: Context,
             offset: int = 0,
             *,
             code: Optional[ErrorCode] = None) -> None:
        self.msg.note(msg, context, offset=offset, code=code)
    def iterable_item_type(self, instance: Instance) -> Type:
        iterable = map_instance_to_supertype(
            instance,
            self.lookup_typeinfo('typing.Iterable'))
        item_type = iterable.args[0]
        if not isinstance(get_proper_type(item_type), AnyType):
            return item_type
        iter_type = get_proper_type(find_member('__iter__', instance, instance, is_operator=True))
        if iter_type and isinstance(iter_type, CallableType):
            ret_type = get_proper_type(iter_type.ret_type)
            if isinstance(ret_type, Instance):
                iterator = map_instance_to_supertype(ret_type,
                                                     self.lookup_typeinfo('typing.Iterator'))
                item_type = iterator.args[0]
        return item_type
    def function_type(self, func: FuncBase) -> FunctionLike:
        return function_type(func, self.named_type('builtins.function'))
    def add_type_map(self, type_map: 'TypeMap', node, t) -> None:
        self.store_type(node, t)
        if type_map is None or any(isinstance(x, UninhabitedType) for x in type_map.values()):
            return
        return
        nodes = list(type_map.keys())
        types = itertools.product(*[x.items for x in type_map.values()])
        for typ in types:
            self.expr_checker.add_infer_type((node,t), list(zip(nodes, typ)))
    def push_type_map(self, type_map: 'TypeMap', node=None, typ=None) -> None:
        if type_map is None or any(len(x) == 0 for x in type_map.values()) :
            self.binder.unreachable()
        else:
            self.binder.put_node(node, typ)
            for expr, type in type_map.items():
                self.binder.put(expr, type)
    def infer_issubclass_maps(self, node: CallExpr,
                              expr: Expression,
                              type_map: Dict[Expression, Type]
                              ) -> Tuple[TypeMap, TypeMap]:
        vartype = type_map[expr]
        type = get_isinstance_type(node.args[1], type_map)
        if isinstance(vartype, TypeVarType):
            vartype = vartype.upper_bound
        vartype = get_proper_type(vartype)
        if isinstance(vartype, UnionType):
            union_list = []
            for t in get_proper_types(vartype.items):
                if isinstance(t, TypeType):
                    union_list.append(t.item)
                else:
                    return {}, {}
            vartype = UnionType(union_list)
        elif isinstance(vartype, TypeType):
            vartype = vartype.item
        elif (isinstance(vartype, Instance) and
                vartype.type.fullname == 'builtins.type'):
            vartype = self.named_type('builtins.object')
        else:
            return {}, {}  
        yes_map, no_map = self.conditional_type_map_with_intersection(expr, vartype, type)
        yes_map, no_map = map(convert_to_typetype, (yes_map, no_map))
        return yes_map, no_map
    def conditional_type_map_with_intersection(self,
                                               expr: Expression,
                                               expr_type: Type,
                                               type_ranges: Optional[List[TypeRange]],
                                               ) -> Tuple[TypeMap, TypeMap]:
        initial_maps = conditional_type_map(expr, expr_type, type_ranges)
        yes_map: TypeMap = initial_maps[0]
        no_map: TypeMap = initial_maps[1]
        if yes_map is not None or type_ranges is None:
            return yes_map, no_map
        expr_type = get_proper_type(expr_type)
        if isinstance(expr_type, UnionType):
            possible_expr_types = get_proper_types(expr_type.relevant_items())
        else:
            possible_expr_types = [expr_type]
        possible_target_types = []
        for tr in type_ranges:
            item = get_proper_type(tr.item)
            if not isinstance(item, Instance) or tr.is_upper_bound:
                return yes_map, no_map
            possible_target_types.append(item)
        out = []
        for v in possible_expr_types:
            if not isinstance(v, Instance):
                return yes_map, no_map
            for t in possible_target_types:
                intersection = self.intersect_instances((v, t), expr)
                if intersection is None:
                    continue
                out.append(intersection)
        if len(out) == 0:
            return None, {}
        new_yes_type = make_simplified_union(out)
        return {expr: new_yes_type}, {}
    def is_writable_attribute(self, node: Node) -> bool:
        if isinstance(node, Var):
            return True
        elif isinstance(node, OverloadedFuncDef) and node.is_property:
            first_item = cast(Decorator, node.items[0])
            return first_item.var.is_settable_property
        else:
            return False
def conditional_type_map(expr: Expression,
                         current_types : Optional[Type],
                         proposed_type_ranges: Optional[List[TypeRange]],
                         ) -> Tuple[TypeMap, TypeMap]:
    """Takes in an expression, the current type of the expression, and a
    proposed type of that expression.
    Returns a 2-tuple: The first element is a map from the expression to
    the proposed type, if the expression can be the proposed type.  The
    second element is a map from the expression to the type it would hold
    if it was not the proposed type, if any. None means bot, {} means top"""
    if proposed_type_ranges:
        no_map = {expr:[]}
        yes_map = {expr:[]}
        proposed_items = [type_range.item for type_range in proposed_type_ranges]
        proposed_type = make_simplified_union(proposed_items)
        if isinstance(proposed_type, AnyType) or isinstance(proposed_type, NoneType):
            return {expr:[]}, {expr:[]}
        for current_type in current_types:
            if current_type:
                if (not any(type_range.is_upper_bound for type_range in proposed_type_ranges)
                and is_proper_subtype(current_type, proposed_type)):
                    yes_map[expr].append(current_type)
                elif not is_overlapping_types(current_type, proposed_type,
                                            prohibit_none_typevar_overlap=True):
                    no_map[expr].append(current_type)
                else:
                    yes_map[expr].append(current_type)
                    no_map[expr].append(current_type)
            else:
                    yes_map[expr].append(proposed_type)
        return yes_map, no_map
    else:
        return {}, {}
def gen_unique_name(base: str, table: SymbolTable) -> str:
    if base not in table:
        return base
    i = 1
    while base + str(i) in table:
        i += 1
    return base + str(i)
def is_true_literal(n: Expression) -> bool:
    return (refers_to_fullname(n, 'builtins.True')
            or isinstance(n, IntExpr) and n.value != 0)
def is_false_literal(n: Expression) -> bool:
    return (refers_to_fullname(n, 'builtins.False')
            or isinstance(n, IntExpr) and n.value == 0)
def is_literal_enum(type_map: Mapping[Expression, Type], n: Expression) -> bool:
    """Returns true if this expression (with the given type context) is an Enum literal.
    For example, if we had an enum:
        class Foo(Enum):
            A = 1
            B = 2
    ...and if the expression 'Foo' referred to that enum within the current type context,
    then the expression 'Foo.A' would be a a literal enum. However, if we did 'a = Foo.A',
    then the variable 'a' would *not* be a literal enum.
    We occasionally special-case expressions like 'Foo.A' and treat them as a single primitive
    unit for the same reasons we sometimes treat 'True', 'False', or 'None' as a single
    primitive unit.
    """
    if not isinstance(n, MemberExpr) or not isinstance(n.expr, NameExpr):
        return False
    parent_type = type_map.get(n.expr)
    member_type = type_map.get(n)
    if member_type is None or parent_type is None:
        return False
    parent_type = get_proper_type(parent_type)
    member_type = get_proper_type(coerce_to_literal(member_type))
    if not isinstance(parent_type, FunctionLike) or not isinstance(member_type, LiteralType):
        return False
    if not parent_type.is_type_obj():
        return False
    return member_type.is_enum_literal() and member_type.fallback.type == parent_type.type_object()
def is_literal_none(n: Expression) -> bool:
    return isinstance(n, NameExpr) and n.fullname == 'builtins.None'
def is_literal_not_implemented(n: Expression) -> bool:
    return isinstance(n, NameExpr) and n.fullname == 'builtins.NotImplemented'
def builtin_item_type(tp: Type) -> Optional[Type]:
    """Get the item type of a builtin container.
    If 'tp' is not one of the built containers (these includes NamedTuple and TypedDict)
    or if the container is not parameterized (like List or List[Any])
    return None. This function is used to narrow optional types in situations like this:
        x: Optional[int]
        if x in (1, 2, 3):
            x + 42  
    Note: this is only OK for built-in containers, where we know the behavior
    of __contains__.
    """
    tp = get_proper_type(tp)
    if isinstance(tp, Instance):
        if tp.type.fullname in [
            'builtins.list', 'builtins.tuple', 'builtins.dict',
            'builtins.set', 'builtins.frozenset',
        ]:
            if not tp.args:
                return None
            if not isinstance(get_proper_type(tp.args[0]), AnyType):
                return tp.args[0]
    elif isinstance(tp, TupleType) and all(not isinstance(it, AnyType)
                                           for it in get_proper_types(tp.items)):
        return make_simplified_union(tp.items)  
    elif isinstance(tp, TypedDictType):
        for base in tp.fallback.type.mro:
            if base.fullname == 'typing.Mapping':
                return map_instance_to_supertype(tp.fallback, base).args[0]
        assert False, 'No Mapping base class found for TypedDict fallback'
    return None
def and_conditional_maps(m1: TypeMap, m2: TypeMap) -> TypeMap:
    """Calculate what information we can learn from the truth of (e1 and e2)
    in terms of the information that we can learn from the truth of e1 and
    the truth of e2.
    """
    if m1 is None or m2 is None:
        return None
    result = m2.copy()
    m2_keys = set(literal_hash(n2) for n2 in m2)
    for n1 in m1:
        if literal_hash(n1) not in m2_keys:
            result[n1] = m1[n1]
    return result
def or_conditional_maps(m1: TypeMap, m2: TypeMap) -> TypeMap:
    """Calculate what information we can learn from the truth of (e1 or e2)
    in terms of the information that we can learn from the truth of e1 and
    the truth of e2.
    """
    if m1 is None:
        return m2
    if m2 is None:
        return m1
    result: Dict[Expression, Type] = {}
    for n1 in m1:
        for n2 in m2:
            if literal_hash(n1) == literal_hash(n2):
                if isinstance(m1[n1], list) and isinstance(m2[n2], list):
                    result[n1] = m1[n1]+m2[n2]
                elif isinstance(m1[n1], set) and isinstance(m2[n2], set):
                    result[n1] = m1[n1]|m2[n2]
                else:
                    result[n1] = {make_simplified_union([m1[n1], m2[n2]])}
    return result
def reduce_conditional_maps(type_maps: List[Tuple[TypeMap, TypeMap]],
                            ) -> Tuple[TypeMap, TypeMap]:
    """Reduces a list containing pairs of if/else TypeMaps into a single pair.
    We "and" together all of the if TypeMaps and "or" together the else TypeMaps. So
    for example, if we had the input:
        [
            ({x: TypeIfX, shared: TypeIfShared1}, {x: TypeElseX, shared: TypeElseShared1}),
            ({y: TypeIfY, shared: TypeIfShared2}, {y: TypeElseY, shared: TypeElseShared2}),
        ]
    ...we'd return the output:
        (
            {x: TypeIfX,   y: TypeIfY,   shared: PseudoIntersection[TypeIfShared1, TypeIfShared2]},
            {shared: Union[TypeElseShared1, TypeElseShared2]},
        )
    ...where "PseudoIntersection[X, Y] == Y" because mypy actually doesn't understand intersections
    yet, so we settle for just arbitrarily picking the right expr's type.
    We only retain the shared expression in the 'else' case because we don't actually know
    whether x was refined or y was refined -- only just that one of the two was refined.
    """
    if len(type_maps) == 0:
        return {}, {}
    elif len(type_maps) == 1:
        return type_maps[0]
    else:
        final_if_map, final_else_map = type_maps[0]
        for if_map, else_map in type_maps[1:]:
            final_if_map = and_conditional_maps(final_if_map, if_map)
            final_else_map = or_conditional_maps(final_else_map, else_map)
        return final_if_map, final_else_map
def convert_to_typetype(type_map: TypeMap) -> TypeMap:
    converted_type_map: Dict[Expression, Type] = {}
    if type_map is None:
        return None
    for expr, typ in type_map.items():
        t = typ
        if isinstance(t, TypeVarType):
            t = t.upper_bound
        if not isinstance(get_proper_type(t), (UnionType, Instance)):
            return {}
        converted_type_map[expr] = TypeType.make_normalized(typ)
    return converted_type_map
def flatten(t: Expression) -> List[Expression]:
    if isinstance(t, TupleExpr) or isinstance(t, ListExpr):
        return [b for a in t.items for b in flatten(a)]
    elif isinstance(t, StarExpr):
        return flatten(t.expr)
    else:
        return [t]
def flatten_type_set(ts:Set[Type]) -> List[Type]:
    ret = set()
    for t in ts:
        ret.update(flatten_types(t))
    return ret
def flatten_types(t: Type) -> List[Type]:
    t = get_proper_type(t)
    if isinstance(t, TupleType):
        return [b for a in t.items for b in flatten_types(a)]
    else:
        return [t]
def get_isinstance_type(expr: Expression,
                        type_map: Dict[Expression, Type]) -> Optional[List[TypeRange]]:
    if isinstance(expr, OpExpr) and expr.op == '|':
        left = get_isinstance_type(expr.left, type_map)
        right = get_isinstance_type(expr.right, type_map)
        if left is None or right is None:
            return None
        return left + right
    all_types = flatten_type_set(type_map[expr])
    types: List[TypeRange] = []
    for typ in all_types:
        if isinstance(typ, FunctionLike) and typ.is_type_obj():
            erased_type = erase_typevars(typ.items[0].ret_type)
            types.append(TypeRange(erased_type, is_upper_bound=False))
        elif isinstance(typ, TypeType):
            types.append(TypeRange(typ.item, is_upper_bound=True))
        elif isinstance(typ, Instance) and typ.type.fullname == 'builtins.type':
            object_type = Instance(typ.type.mro[-1], [])
            types.append(TypeRange(object_type, is_upper_bound=True))
        elif isinstance(typ, AnyType):
            types.append(TypeRange(typ, is_upper_bound=False))
        else:  
            return None
    if not types:
        return None
    return types
def expand_func(defn: FuncItem, map: Dict[TypeVarId, Type]) -> FuncItem:
    visitor = TypeTransformVisitor(map)
    ret = defn.accept(visitor)
    assert isinstance(ret, FuncItem)
    return ret
class TypeTransformVisitor(TransformVisitor):
    def __init__(self, map: Dict[TypeVarId, Type]) -> None:
        super().__init__()
        self.map = map
    def type(self, type: Type) -> Type:
        return expand_type(type, self.map)
def infer_operator_assignment_method(typ: Type, operator: str) -> Tuple[bool, str]:
    """Determine if operator assignment on given value type is in-place, and the method name.
    For example, if operator is '+', return (True, '__iadd__') or (False, '__add__')
    depending on which method is supported by the type.
    """
    typ = get_proper_type(typ)
    method = operators.op_methods[operator]
    if isinstance(typ, Instance):
        if operator in operators.ops_with_inplace_method:
            inplace_method = '__i' + method[2:]
            if typ.type.has_readable_member(inplace_method):
                return True, inplace_method
    return False, method
def is_valid_inferred_type(typ: Type) -> bool:
    """Is an inferred type valid?
    Examples of invalid types include the None type or List[<uninhabited>].
    When not doing strict Optional checking, all types containing None are
    invalid.  When doing strict Optional checking, only None and types that are
    incompletely defined (i.e. contain UninhabitedType) are invalid.
    """
    if isinstance(get_proper_type(typ), (NoneType, UninhabitedType)):
        return False
    return not typ.accept(NothingSeeker())
class NothingSeeker(TypeQuery[bool]):
    def __init__(self) -> None:
        super().__init__(any)
    def visit_uninhabited_type(self, t: UninhabitedType) -> bool:
        return t.ambiguous
class CheckerScope:
    stack: List[Union[TypeInfo, FuncItem, MypyFile]]
    def __init__(self, module: MypyFile) -> None:
        self.stack = [module]
    def top_function(self) -> Optional[FuncItem]:
        for e in reversed(self.stack):
            if isinstance(e, FuncItem):
                return e
        return None
    def top_non_lambda_function(self) -> Optional[FuncItem]:
        for e in reversed(self.stack):
            if isinstance(e, FuncItem) and not isinstance(e, LambdaExpr):
                return e
        return None
    def active_class(self) -> Optional[TypeInfo]:
        if isinstance(self.stack[-1], TypeInfo):
            return self.stack[-1]
        return None
    def enclosing_class(self) -> Optional[TypeInfo]:
        top = self.top_function()
        assert top, "This method must be called from inside a function"
        index = self.stack.index(top)
        assert index, "CheckerScope stack must always start with a module"
        enclosing = self.stack[index - 1]
        if isinstance(enclosing, TypeInfo):
            return enclosing
        return None
    def active_self_type(self) -> Optional[Union[Instance, TupleType]]:
        """An instance or tuple type representing the current class.
        This returns None unless we are in class body or in a method.
        In particular, inside a function nested in method this returns None.
        """
        info = self.active_class()
        if not info and self.top_function():
            info = self.enclosing_class()
        if info:
            return fill_typevars(info)
        return None
    @contextmanager
    def push_function(self, item: FuncItem) -> Iterator[None]:
        self.stack.append(item)
        yield
        self.stack.pop()
    @contextmanager
    def push_class(self, info: TypeInfo) -> Iterator[None]:
        self.stack.append(info)
        yield
        self.stack.pop()
@contextmanager
def nothing() -> Iterator[None]:
    yield
TKey = TypeVar('TKey')
TValue = TypeVar('TValue')
class DisjointDict(Generic[TKey, TValue]):
    """An variation of the union-find algorithm/data structure where instead of keeping
    track of just disjoint sets, we keep track of disjoint dicts -- keep track of multiple
    Set[Key] -> Set[Value] mappings, where each mapping's keys are guaranteed to be disjoint.
    This data structure is currently used exclusively by 'group_comparison_operands' below
    to merge chains of '==' and 'is' comparisons when two or more chains use the same expression
    in best-case O(n), where n is the number of operands.
    Specifically, the `add_mapping()` function and `items()` functions will take on average
    O(k + v) and O(n) respectively, where k and v are the number of keys and values we're adding
    for a given chain. Note that k <= n and v <= n.
    We hit these average/best-case scenarios for most user code: e.g. when the user has just
    a single chain like 'a == b == c == d == ...' or multiple disjoint chains like
    'a==b < c==d < e==f < ...'. (Note that a naive iterative merging would be O(n^2) for
    the latter case).
    In comparison, this data structure will make 'group_comparison_operands' have a worst-case
    runtime of O(n*log(n)): 'add_mapping()' and 'items()' are worst-case O(k*log(n) + v) and
    O(k*log(n)) respectively. This happens only in the rare case where the user keeps repeatedly
    making disjoint mappings before merging them in a way that persistently dodges the path
    compression optimization in '_lookup_root_id', which would end up constructing a single
    tree of height log_2(n). This makes root lookups no longer amoritized constant time when we
    finally call 'items()'.
    """
    def __init__(self) -> None:
        self._key_to_id: Dict[TKey, int] = {}
        self._id_to_parent_id: Dict[int, int] = {}
        self._root_id_to_values: Dict[int, Set[TValue]] = {}
    def add_mapping(self, keys: Set[TKey], values: Set[TValue]) -> None:
        """Adds a 'Set[TKey] -> Set[TValue]' mapping. If there already exists a mapping
        containing one or more of the given keys, we merge the input mapping with the old one.
        Note that the given set of keys must be non-empty -- otherwise, nothing happens.
        """
        if len(keys) == 0:
            return
        subtree_roots = [self._lookup_or_make_root_id(key) for key in keys]
        new_root = subtree_roots[0]
        root_values = self._root_id_to_values[new_root]
        root_values.update(values)
        for subtree_root in subtree_roots[1:]:
            if subtree_root == new_root or subtree_root not in self._root_id_to_values:
                continue
            self._id_to_parent_id[subtree_root] = new_root
            root_values.update(self._root_id_to_values.pop(subtree_root))
    def items(self) -> List[Tuple[Set[TKey], Set[TValue]]]:
        root_id_to_keys: Dict[int, Set[TKey]] = {}
        for key in self._key_to_id:
            root_id = self._lookup_root_id(key)
            if root_id not in root_id_to_keys:
                root_id_to_keys[root_id] = set()
            root_id_to_keys[root_id].add(key)
        output = []
        for root_id, keys in root_id_to_keys.items():
            output.append((keys, self._root_id_to_values[root_id]))
        return output
    def _lookup_or_make_root_id(self, key: TKey) -> int:
        if key in self._key_to_id:
            return self._lookup_root_id(key)
        else:
            new_id = len(self._key_to_id)
            self._key_to_id[key] = new_id
            self._id_to_parent_id[new_id] = new_id
            self._root_id_to_values[new_id] = set()
            return new_id
    def _lookup_root_id(self, key: TKey) -> int:
        i = self._key_to_id[key]
        while i != self._id_to_parent_id[i]:
            new_parent = self._id_to_parent_id[self._id_to_parent_id[i]]
            self._id_to_parent_id[i] = new_parent
            i = new_parent
        return i
def group_comparison_operands(pairwise_comparisons: Iterable[Tuple[str, Expression, Expression]],
                              operand_to_literal_hash: Mapping[int, Key],
                              operators_to_group: Set[str],
                              ) -> List[Tuple[str, List[int]]]:
    """Group a series of comparison operands together chained by any operand
    in the 'operators_to_group' set. All other pairwise operands are kept in
    groups of size 2.
    For example, suppose we have the input comparison expression:
        x0 == x1 == x2 < x3 < x4 is x5 is x6 is not x7 is not x8
    If we get these expressions in a pairwise way (e.g. by calling ComparisionExpr's
    'pairwise()' method), we get the following as input:
        [('==', x0, x1), ('==', x1, x2), ('<', x2, x3), ('<', x3, x4),
         ('is', x4, x5), ('is', x5, x6), ('is not', x6, x7), ('is not', x7, x8)]
    If `operators_to_group` is the set {'==', 'is'}, this function will produce
    the following "simplified operator list":
       [("==", [0, 1, 2]), ("<", [2, 3]), ("<", [3, 4]),
        ("is", [4, 5, 6]), ("is not", [6, 7]), ("is not", [7, 8])]
    Note that (a) we yield *indices* to the operands rather then the operand
    expressions themselves and that (b) operands used in a consecutive chain
    of '==' or 'is' are grouped together.
    If two of these chains happen to contain operands with the same underlying
    literal hash (e.g. are assignable and correspond to the same expression),
    we combine those chains together. For example, if we had:
        same == x < y == same
    ...and if 'operand_to_literal_hash' contained the same values for the indices
    0 and 3, we'd produce the following output:
        [("==", [0, 1, 2, 3]), ("<", [1, 2])]
    But if the 'operand_to_literal_hash' did *not* contain an entry, we'd instead
    default to returning:
        [("==", [0, 1]), ("<", [1, 2]), ("==", [2, 3])]
    This function is currently only used to assist with type-narrowing refinements
    and is extracted out to a helper function so we can unit test it.
    """
    groups: Dict[str, DisjointDict[Key, int]] = {op: DisjointDict() for op in operators_to_group}
    simplified_operator_list: List[Tuple[str, List[int]]] = []
    last_operator: Optional[str] = None
    current_indices: Set[int] = set()
    current_hashes: Set[Key] = set()
    for i, (operator, left_expr, right_expr) in enumerate(pairwise_comparisons):
        if last_operator is None:
            last_operator = operator
        if current_indices and (operator != last_operator or operator not in operators_to_group):
            if len(current_hashes) == 0:
                simplified_operator_list.append((last_operator, sorted(current_indices)))
            else:
                groups[last_operator].add_mapping(current_hashes, current_indices)
            last_operator = operator
            current_indices = set()
            current_hashes = set()
        current_indices.add(i)
        current_indices.add(i + 1)
        if operator in operators_to_group:
            left_hash = operand_to_literal_hash.get(i)
            if left_hash is not None:
                current_hashes.add(left_hash)
            right_hash = operand_to_literal_hash.get(i + 1)
            if right_hash is not None:
                current_hashes.add(right_hash)
    if last_operator is not None:
        if len(current_hashes) == 0:
            simplified_operator_list.append((last_operator, sorted(current_indices)))
        else:
            groups[last_operator].add_mapping(current_hashes, current_indices)
    for operator, disjoint_dict in groups.items():
        for keys, indices in disjoint_dict.items():
            simplified_operator_list.append((operator, sorted(indices)))
    simplified_operator_list.sort(key=lambda item: item[1][0])
    return simplified_operator_list
def is_static(func: Union[FuncBase, Decorator]) -> bool:
    if isinstance(func, Decorator):
        return is_static(func.func)
    elif isinstance(func, FuncBase):
        return func.is_static
    assert False, "Unexpected func type: {}".format(type(func))
def is_subtype_no_promote(left: Type, right: Type) -> bool:
    return is_subtype(left, right, ignore_promotions=True)
def is_overlapping_types_no_promote(left: Type, right: Type) -> bool:
    return is_overlapping_types(left, right, ignore_promotions=True)
def is_private(node_name: str) -> bool:
    return node_name.startswith('__') and not node_name.endswith('__')
def has_bool_item(typ: ProperType) -> bool:
    if is_named_instance(typ, 'builtins.bool'):
        return True
    if isinstance(typ, UnionType):
        return any(is_named_instance(item, 'builtins.bool')
                   for item in typ.items)
    return False
def collapse_walrus(e: Expression) -> Expression:
    """If an expression is an AssignmentExpr, pull out the assignment target.
    We don't make any attempt to pull out all the targets in code like `x := (y := z)`.
    We could support narrowing those if that sort of code turns out to be common.
    """
    if isinstance(e, AssignmentExpr):
        return e.target
    return e
