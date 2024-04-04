from collections import defaultdict
from subprocess import call
from torch import narrow
from extyper.solve import solve_constraints
from extyper.types import TypeAliasType, is_generic
from extyper.util import unnamed_function
from extyper.backports import OrderedDict, nullcontext
from contextlib import contextmanager
import itertools
import itertools
import time
from typing import (
    Any, cast, Dict, Set, List, Tuple, Callable, Union, Optional, Sequence, Iterator
)
from typing_extensions import ClassVar, Final, overload
from extyper.errors import report_internal_error
from extyper.typeanal import (
    has_any_from_unimported_type, check_for_explicit_any, remove_dups, set_any_tvars, expand_type_alias,
    make_optional_type,
)
from extyper.types import (
    Type, AnyType, CallableType, Overloaded, NoneType, TypeVarId, TypeVarType,
    TupleType, TypedDictType, Instance, ErasedType, UnionType, MaybeTypes,
    PartialType, DeletedType, UninhabitedType, TypeType, TypeOfAny, LiteralType, LiteralValue, copy_type,
    is_named_instance, FunctionLike, ParamSpecType,
    StarType, is_optional, remove_optional, is_generic_instance, get_proper_type, ProperType,
    get_proper_types, flatten_nested_unions
)
from extyper.nodes import (
    NameExpr, RefExpr, Var, FuncDef, OverloadedFuncDef, TypeInfo, CallExpr,
    MemberExpr, IntExpr, StrExpr, BytesExpr, UnicodeExpr, FloatExpr,
    OpExpr, UnaryExpr, IndexExpr, CastExpr, RevealExpr, TypeApplication, ListExpr,
    TupleExpr, DictExpr, LambdaExpr, SuperExpr, SliceExpr, Context, Expression,
    ListComprehension, GeneratorExpr, SetExpr, MypyFile, Decorator,
    ConditionalExpr, ComparisonExpr, TempNode, SetComprehension, AssignmentExpr,
    DictionaryComprehension, ComplexExpr, EllipsisExpr, StarExpr, AwaitExpr, YieldExpr,
    YieldFromExpr, TypedDictExpr, PromoteExpr, NewTypeExpr, NamedTupleExpr, TypeVarExpr,
    TypeAliasExpr, BackquoteExpr, EnumCallExpr, TypeAlias, SymbolNode, PlaceholderNode,
    ParamSpecExpr,
    ArgKind, ARG_POS, ARG_NAMED, ARG_STAR, ARG_STAR2, LITERAL_TYPE, REVEAL_TYPE, Argument
)
from extyper.literals import literal
from extyper import constraints, nodes
from extyper import operators
import extyper.checker
from extyper import types
from extyper.sametypes import is_same_type
from extyper.erasetype import replace_meta_vars, erase_type, remove_instance_last_known_values
from extyper.maptype import map_instance_to_supertype
from extyper.messages import MessageBuilder
from extyper import message_registry
from extyper.infer import infer_type_arguments, infer_function_type_arguments
from extyper import join
from extyper.meet import narrow_declared_type, is_overlapping_types
from extyper.subtypes import is_subtype, is_proper_subtype
from extyper import applytype
from extyper import erasetype
from extyper.checkmember import analyze_member_access, type_object_type
from extyper.argmap import ArgTypeExpander, map_actuals_to_formals, map_formals_to_actuals
from extyper.checkstrformat import StringFormatterChecker
from extyper.expandtype import expand_type, expand_type_by_instance, freshen_function_type_vars
from extyper.util import split_module_names
from extyper.typevars import fill_typevars
from extyper.visitor import ExpressionVisitor
from extyper.plugin import (
    Plugin,
    MethodContext, MethodSigContext,
    FunctionContext, FunctionSigContext,
)
from extyper.typeops import (
    tuple_fallback, make_simplified_union, true_only, false_only, erase_to_union_or_bound,
    function_type, callable_type, try_getting_str_literals, custom_special_method,
    is_literal_type_like,
)
import extyper.errorcodes as codes
from extyper.traverser import TraverserVisitor
from copy import deepcopy
ArgChecker = Callable[[Type,
                       Type,
                       ArgKind,
                       Type,
                       int,
                       int,
                       CallableType,
                       Optional[Type],
                       Context,
                       Context,
                       MessageBuilder],
                      None]
MAX_UNIONS: Final = 5
OVERLAPPING_TYPES_WHITELIST: Final = [
    "builtins.set",
    "builtins.frozenset",
    "typing.KeysView",
    "typing.ItemsView",
]

def extract_refexpr_names(expr: RefExpr) -> Set[str]:
    output: Set[str] = set()
    while isinstance(expr.node, MypyFile) or expr.fullname is not None:
        if isinstance(expr.node, MypyFile) and expr.fullname is not None:
            output.add(expr.fullname)
        if isinstance(expr, NameExpr):
            is_suppressed_import = isinstance(expr.node, Var) and expr.node.is_suppressed_import
            if isinstance(expr.node, TypeInfo):
                output.update(split_module_names(expr.node.module_name))
            elif expr.fullname is not None and '.' in expr.fullname and not is_suppressed_import:
                output.add(expr.fullname.rsplit('.', 1)[0])
            break
        elif isinstance(expr, MemberExpr):
            if isinstance(expr.expr, RefExpr):
                expr = expr.expr
            else:
                break
        else:
            raise AssertionError("Unknown RefExpr subclass: {}".format(type(expr)))
    return output
def get_identity(func, var):
    try:
        if func is not None and var is not None:
            return func.fullname + '.' + str(var.fullname)
    except Exception:
        return "no input identity"
def detect_circle(infer_map):
    for x in infer_map:
        worklist = [x]
        cnt = 0
        while worklist:
            cnt += 1
            if cnt >= 10000:
                print('cicle')
            reasons = worklist.pop(0)
            options = [] 
            try:
                if not any([reason in infer_map for reason in reasons]):
                    continue
            except Exception:
                pass
            for reason in reasons:
                possible_further_reason = [] 
                if reason not in infer_map:
                    possible_further_reason.append([reason]) 
                else:
                    for stubs_for_this_reason in infer_map[reason]: 
                        if stubs_for_this_reason not in possible_further_reason:
                            possible_further_reason.append(stubs_for_this_reason)
                options.append(possible_further_reason)
            now_component_reasons = options[0] 
            for now_reasons in options[1:]:
                n_nexts = []
                for possible_reason in now_reasons:
                    for n in now_component_reasons:
                        new_n = [x for x in n]
                        for r in possible_reason:
                            if r not in new_n:
                                new_n.append(r)
                        n_nexts.append(new_n)
                now_component_reasons = n_nexts
            worklist.extend(now_component_reasons)
def detect_dup_id_pairs(reason):
    node_types = defaultdict(set)
    for x in reason:
        node_types[x[0]].add(x[1])
    if all(len(x)<=1 for x in node_types.values()):
        reasons = [(x[0],list(x[1])[0]) for x in node_types.items()]
        return reasons
    else:
        return None
def remove_dups_for_reason(now_component_reasons):
    reasons = []
    for reason in now_component_reasons:
        node_types = defaultdict(set)
        for x in reason:
            node_types[x[0]].add(x[1])
        if all(len(x)<=1 for x in node_types.values()):
            reasons.append(reason)
        else:
            pass
    return reasons
def get_ground_pairs(dp_dag, infer_map, init_pairs, combination_limits = 1024):
    def same_node(reasons, stubs_for_this_reason):
        try:
            node_types = {x[0]:x[1] for x in reasons}
            for node, typ in stubs_for_this_reason:
                if node in node_types and isinstance(node, Argument) and node_types[node] != typ:
                    return True
            return False
        except Exception:
            pass
    init_pairs = tuple(init_pairs)
    if init_pairs in dp_dag:
        return dp_dag[init_pairs]
    ret = []
    worklist = set([tuple(init_pairs)])
    returns = set()
    while worklist:
        reasons = worklist.pop()
        options = [] 
        if not any([reason in infer_map for reason in reasons]):
            returns.add(reasons)
            continue
        for reason in reasons:
            possible_further_reason = [] 
            if reason not in infer_map:
                possible_further_reason.append([reason]) 
            else:
                for stubs_for_this_reason in infer_map[reason]: 
                    grounds_for_this_stub = get_ground_pairs(dp_dag, infer_map, stubs_for_this_reason, combination_limits)
                    if len(grounds_for_this_stub) > 0:
                        if grounds_for_this_stub not in possible_further_reason:
                            possible_further_reason.extend(grounds_for_this_stub)
            options.append(possible_further_reason)
        now_component_reasons = options[0] 
        def calculate_overlapping_nodes(P1, P2):
            nodes_1 = set([x for x, y in P1])
            nodes_2 = set([x for x, y in P2])
            overlapping_nodes = set.intersection(nodes_1, nodes_2)
            return overlapping_nodes
        def project_pairs(overlapping_nodes, pairs):
            key = set()
            for p in pairs:
                node, _ = p
                if node in overlapping_nodes:
                    key.add(p)
            return tuple(sorted(key, key=lambda x:str(x)))
        def project_pairs_set(overlapping_nodes, opts):
            mapping = defaultdict(list)
            for opt in opts:
                key = project_pairs(overlapping_nodes, opt)
                mapping[key].append(opt)
            return mapping
        for i in range(1, len(options)):
            if len(now_component_reasons) == 0 or len(options[i]) == 0:
                now_component_reasons = []
                break
            n_nexts = []
            overlapping_nodes = calculate_overlapping_nodes(now_component_reasons[0], options[i][0])
            ovnodes_2_reasons = project_pairs_set(overlapping_nodes, options[i])
            for n in now_component_reasons:
                k = project_pairs(overlapping_nodes, n)
                for n2 in ovnodes_2_reasons[k]:
                    new_n = list(set(list(n) + list(n2)))
                    n_nexts.append(new_n)
            now_component_reasons = n_nexts
        returns.update(set([tuple(x) for x in now_component_reasons]))
    dp_dag[init_pairs] = list(set([tuple(x) for x in returns]))
    remove_dups_for_reason(returns)
    
    return list(set([tuple(x) for x in returns]))[:combination_limits] 
class ExpressionInferencer(ExpressionVisitor[Type]):
    """Expression type checker.
    This class works closely together with checker.TypeChecker.
    """
    chk: "extyper.checker.TypeChecker"
    msg: MessageBuilder
    type_context: List[Optional[Type]]
    strfrm_checker: StringFormatterChecker
    plugin: Plugin
    def __init__(self,
                 chk: 'extyper.checker.TypeChecker',
                 msg: MessageBuilder,
                 plugin: Plugin, union_errors=None, incompatible=None, single_incompatible = None, infer_dependency_map=None, added_attr=None, message=None) -> None:
        self.chk = chk
        self.msg = msg
        self.plugin = plugin
        self.type_context = [None]
        self.type_overrides: Dict[Expression, Type] = {}
        self.strfrm_checker = StringFormatterChecker(self, self.chk, self.msg)
        self.union_errors = union_errors
        self.incompatible = incompatible
        self.single_incompatible = single_incompatible
        self.added_attr = added_attr
        self.reason = []
        self.infer_dependency_map = infer_dependency_map
        self.local_infer_map = defaultdict(set) 
        self.node_infer_map = {}
        self.message = message
        self.generic_indices = None
        self.generic_arg_types = None
        self.temp_nodes = {}
    def get_temp_nodes(self, typ, context):
        if (typ, context) not in self.temp_nodes:
            self.temp_nodes[(typ, context)] = TempNode(typ, context=context)
        return self.temp_nodes[(typ, context)]
    def add_path_constrains(self, from_ids):
        path_constraints = [x.record for x in self.chk.binder.frames if x.record is not None]
        from_ids.extend(path_constraints)
    def update_local_infer_map(self, to_node, to_typ, from_ids):
        """
            from_ids is [[(node, t)]]
        """
        self.add_path_constrains(from_ids)
        if len(from_ids) == 0:
            return
        id_to = (to_node, to_typ)
        from_ids = set([tuple(x) for x in from_ids])
        if id_to not in self.local_infer_map:
            self.local_infer_map[id_to] = set()
        self.local_infer_map[id_to].update(from_ids)
    def get_identity_of_var(self, var):
        return get_identity(self.chk.scope.top_function(), var)
    def get_ground_id_pair(self, var, typ):
        id_pairs = [(var, typ)]
        id_pairs =  get_ground_pairs(self.chk.dp_dag, self.local_infer_map, id_pairs, self.chk.combination_limits)
        return id_pairs
    def add_incompatible_from_pairs(self, id_pairs):
        # id_pairs = [(node, typ) for node, typ in id_pairs if isinstance(node, Argument)]
        for fix_pair in id_pairs:
            againist_pairs = [x for x in id_pairs]
            againist_pairs.remove(fix_pair)
            if len(againist_pairs) == 0:
                identity = fix_pair[0]
                typ = fix_pair[1]
                if identity not in self.single_incompatible:
                    self.single_incompatible[identity] = []
                self.single_incompatible[identity].append(typ)
            else:
                if fix_pair not in self.incompatible:
                    self.incompatible[fix_pair] = set()
                self.incompatible[fix_pair].add(tuple(againist_pairs))
    def add_improvement(self, v, t=None):
        self.chk.improvement.add((v, t))
    def add_improvement_from_pair(self, var, typ):
        pairs = self.get_ground_id_pair(var, typ)
        for ground_pairs in pairs:
            for ground_pair in ground_pairs:
                v, t = ground_pair
                self.add_improvement_from_type(v, t)
    def add_improvement_from_type(self, v, t):
        if self.chk.is_checking:
            return
        self.add_improvement(v, t)
    def add_incompatible(self, var1, typ1, var2, typ2):
        self.add_improvement_from_pair(var1, typ1)
        self.add_improvement_from_pair(var2, typ2)
        start = time.time()
        if self.chk.is_checking:
            return
        id_pair1s = self.get_ground_id_pair(var1, typ1)
        id_pair2s = self.get_ground_id_pair(var2, typ2)
        for id_pair1 in id_pair1s:
            for id_pair2 in id_pair2s:
                id_pairs = id_pair1 + id_pair2
                # id_pairs = [(node, typ) for node, typ in id_pairs if isinstance(node, Argument)]
                id_pairs = detect_dup_id_pairs(id_pairs)
                if id_pairs is None:
                    continue
                for fix_pair in id_pairs:
                    againist_pairs = [x for x in id_pairs]
                    againist_pairs.remove(fix_pair)
                    if len(againist_pairs) == 0:
                        identity = fix_pair[0]
                        typ = fix_pair[1]
                        if identity not in self.single_incompatible:
                            self.single_incompatible[identity] = []
                        self.single_incompatible[identity].append(typ)
                    else:
                        if fix_pair not in self.incompatible:
                            self.incompatible[fix_pair] = set()
                        self.incompatible[fix_pair].add(tuple(againist_pairs))
    def add_single_incompatible(self, var1, typ1):
        if self.chk.is_checking:
            return
        self.add_improvement_from_pair(var1, typ1)
        ret = self.get_ground_id_pair(var1, typ1)
        for possibility in ret:
            self.add_incompatible_from_pairs(possibility)
    def visit_name_expr(self, e: NameExpr) -> Set[Type]:
        if isinstance(e, TempNode):
            result = self.analyze_ref_expr(e)
            return result
        self.chk.module_refs.update(extract_refexpr_names(e))
        result = self.analyze_ref_expr(e)
        return self.narrow_type_from_binder(e, result)
    def analyze_ref_expr(self, e: RefExpr, lvalue: bool = False, temp_rhs = None) -> Set[Type]:
        if isinstance(e, TempNode):
            result = AnyType(0)
            node = e.context.node
            if isinstance(node, Var):
                if self.chk.in_var_node(e):
                    def_node = self.chk.get_var_node(e)
                    real_types = []
                    assert def_node in self.chk.type_map, "error"
                    if def_node in self.chk.type_map:
                        for typ in self.chk.type_map[def_node]:
                            self.add_infer_type((e, typ), [(def_node, typ)])
                        return {result}
                else:
                    return {e.type}
            else:
                return {e.type}
        result = None
        node = e.node
        if isinstance(e, NameExpr) and e.is_special_form:
            return {AnyType(TypeOfAny.special_form)}
        if isinstance(node, Var):
            if node.type:
                result = {node.type}
                self.chk.update_var_node(e)
                self.chk.store_type(e, {node.type})
            elif self.chk.in_var_node(e):
                def_node = self.chk.get_var_node(e)
                real_types = []
                if def_node in self.chk.type_map:
                    if temp_rhs:
                        named_left = temp_rhs
                    else:
                        named_left = e
                    if def_node in self.chk.type_map:
                        original_types = self.chk.type_map[def_node]
                        for original_type in original_types:
                            self.add_infer_type((named_left, original_type),[(def_node, original_type)])
                        real_types.extend(original_types)
                if len(real_types) == 0:
                    real_types.append(AnyType(0))
                result = real_types
            else:
                result = {AnyType(0)}
        elif isinstance(node, FuncDef):
            if node == self.chk.scope.top_function():
                return {AnyType(0)}
            if node.type is None and (node in self.chk.func_candidates or node in self.chk.manager.func_candidates):
                self.chk.handle_cannot_determine_type(node.name, None)
            result = {function_type(node, self.named_type('builtins.function'))}
        elif isinstance(node, OverloadedFuncDef) and node.type is not None:
            result = {node.type}
        elif isinstance(node, TypeInfo):
            result = type_object_type(node, self.named_type)
            if (isinstance(result, CallableType) and
                    isinstance(result.ret_type, Instance)):  
                result.ret_type.line = e.line
                result.ret_type.column = e.column
            if isinstance(get_proper_type(self.type_context[-1]), TypeType):
                result = {erasetype.erase_typevars(result)}
        elif isinstance(node, MypyFile):
            try:
                result = {self.named_type('types.ModuleType')}
            except KeyError:
                result = {self.named_type('builtins.object')}
        elif isinstance(node, Decorator):
            result = {self.analyze_var_ref(node.var, e)}
        elif isinstance(node, TypeAlias):
            result = {AnyType(0)}
        elif isinstance(node, (TypeVarExpr, ParamSpecExpr)):
            result = {self.object_type()}
        else:
            result = {AnyType(TypeOfAny.from_error)}
        assert result is not None
        return result
    def add_infer_type(self, typ, from_ids, node_only=False, not_node=False, self_infer=False):
        if any(x[0] == typ[0] for x in from_ids) and not self_infer:
            return
        if len(from_ids) == 0:
            return
        if not not_node:
            onode = typ[0]
            inodes = [x[0] for x in from_ids]
            self.node_infer_map[onode] = inodes
        if node_only:
            return True
        if typ not in self.local_infer_map:
            self.local_infer_map[typ] = set()
        self.local_infer_map[typ].add(tuple(from_ids))
    def analyze_var_ref(self, var: Var, context: Context) -> Type:
        return AnyType(0)
    def visit_call_expr(self, e: CallExpr) -> Set[Type]:
        if e.analyzed:
            if isinstance(e.analyzed, NamedTupleExpr) and not e.analyzed.is_typed:
                self.visit_call_expr_inner(e)
            return self.accept(e.analyzed, self.type_context[-1])
        return self.visit_call_expr_inner(e)
    def visit_call_expr_inner(self, e: CallExpr) -> Set[Type]:
        self.try_infer_partial_type(e)
        type_context = None
        callee_types = self.accept(e.callee, type_context)
        object_type = None
        member = None
        fullname = None
        if isinstance(e.callee, RefExpr):
            fullname = e.callee.fullname
            if isinstance(e.callee.node, TypeAlias):
                target = get_proper_type(e.callee.node.target)
                if isinstance(target, Instance):
                    fullname = target.type.fullname
            if (fullname is None
                    and isinstance(e.callee, MemberExpr)
                    and e.callee.expr in self.chk.type_map):
                member = e.callee.name
                object_type = self.chk.type_map[e.callee.expr]
        ret_types = []
        softs = ['Instance']
        rejects_collection = []
        for callee_type in callee_types:
            corrects = []
            rejects = []
            ret_type = self.check_call_expr_with_callee_type(callee_type, e, fullname,
                                                            object_type, member, corrects = corrects, rejects = rejects)
            rejects_collection.append(rejects)
            if not self.chk.is_checking:
                for pair in rejects:
                    if hasattr(callee_type, "name") and callee_type.name not in softs:
                        self.add_incompatible(pair[0], pair[1], e.callee, callee_type)
            if len(corrects) > 0 and not self.chk.is_checking:
                c0 = next(iter(corrects))
                if len(corrects) > 0 and len(c0) > 0 and (len(c0) == 1 or isinstance(c0[1], Tuple)):
                    assert len(ret_type) == 1
                    ret = next(iter(ret_type))
                    c000 = next(iter(c0[0]))
                    if isinstance(c000, int):
                        ok = True
                        self.add_infer_type((e, ret), [(e.callee, callee_type)])
                    else:
                        ok_args = itertools.product(*corrects)
                        k = 0
                        for args in ok_args:
                            k += 1
                            if k > self.chk.combination_limits:
                                break
                            ok = True
                            args = tuple([(x[0], x[1]) for x in args])
                            self.add_infer_type((e, ret), [(e.callee, callee_type)] + list(args))
                elif len(corrects) > 0 and len(c0) > 0:
                    for correct in corrects:
                        args, ret = correct
                        ok = True
                        if isinstance(args, int):
                            self.add_infer_type((e, ret), [(e.callee, callee_type)])
                            break    
                        self.add_infer_type((e, ret), [(e.callee, callee_type)] + list(args))
            ret_types.extend(ret_type)
        return ret_types
    def method_fullname(self, object_type: Type, method_name: str) -> Optional[str]:
        """Convert a method name to a fully qualified name, based on the type of the object that
        it is invoked on. Return `None` if the name of `object_type` cannot be determined.
        """
        object_type = get_proper_type(object_type)
        if isinstance(object_type, CallableType) and object_type.is_type_obj():
            object_type = get_proper_type(object_type.ret_type)
        elif isinstance(object_type, TypeType):
            object_type = object_type.item
        type_name = None
        if isinstance(object_type, Instance):
            type_name = object_type.type.fullname
        elif isinstance(object_type, (TypedDictType, LiteralType)):
            info = object_type.fallback.type.get_containing_type_info(method_name)
            type_name = info.fullname if info is not None else None
        elif isinstance(object_type, TupleType):
            type_name = tuple_fallback(object_type).type.fullname
        if type_name is not None:
            return '{}.{}'.format(type_name, method_name)
        else:
            return None
    def get_partial_self_var(self, expr: MemberExpr) -> Optional[Var]:
        if not (isinstance(expr.expr, NameExpr) and
                isinstance(expr.expr.node, Var) and expr.expr.node.is_self):
            return None
        info = self.chk.scope.enclosing_class()
        if not info or expr.name not in info.names:
            return None
        sym = info.names[expr.name]
        if isinstance(sym.node, Var) and isinstance(sym.node.type, PartialType):
            return sym.node
        return None
    item_args: ClassVar[Dict[str, List[str]]] = {
        "builtins.list": ["append"],
        "builtins.set": ["add", "discard"],
    }
    container_args: ClassVar[Dict[str, Dict[str, List[str]]]] = {
        "builtins.list": {"extend": ["builtins.list"]},
        "builtins.dict": {"update": ["builtins.dict"]},
        "collections.OrderedDict": {"update": ["builtins.dict"]},
        "builtins.set": {"update": ["builtins.set", "builtins.list"]},
    }
    def get_partial_named_node(self, ref: RefExpr) -> Optional[Tuple[Var, Dict[Var, Context]]]:
        if isinstance(ref, NameExpr):
            if isinstance(ref.node, Var):
                if ref.node.type is not None:
                    return None
                if self.chk.in_var_node(ref):
                    types = self.chk.type_map[self.chk.get_var_node(ref)]
                    return self.chk.get_var_node(ref), types
            else:
                types = []
                return ref, types
        else:
            return None
    def try_infer_partial_type(self, e: CallExpr) -> None:
        if not isinstance(e.callee, MemberExpr):
            return
        callee = e.callee
        if isinstance(callee.expr, RefExpr):
            ret = self.get_partial_named_node(callee.expr)
            if ret is None:
                return
            var, partial_types = ret
            typ = self.try_infer_partial_value_type_from_call(e, callee.name, partial_types, var)
        elif isinstance(callee.expr, IndexExpr) and isinstance(callee.expr.base, RefExpr):
            return 
    def get_partial_var(self, ref: RefExpr) -> Optional[Tuple[Var, Dict[Var, Context]]]:
        var = ref.node
        if var is None and isinstance(ref, MemberExpr):
            var = self.get_partial_self_var(ref)
        if not isinstance(var, Var):
            return None
        partial_types = self.chk.find_partial_types(var)
        if partial_types is None:
            return None
        return var, partial_types
    def get_var_node(self, var):
        if var in self.chk.var_node:
            nodes = self.chk.var_node[var]
            if len(nodes) > 0:
                node = nodes[0]
                return node
        return None 
    def try_infer_partial_value_type_from_call(
            self,
            e: CallExpr,
            methodname: str,
            partial_types, 
            node) -> Optional[Instance]:
        if self.chk.current_node_deferred:
            return None
        new_types = []
        for partial_type in partial_types:
            if not isinstance(partial_type, PartialType) or partial_type.type == None:
                new_types.append(partial_type)
                continue
            if partial_type.value_type:
                typename = partial_type.value_type.type.fullname
            else:
                assert partial_type.type is not None
                typename = partial_type.type.fullname
            if (typename in self.item_args and methodname in self.item_args[typename]
                    and e.arg_kinds == [ARG_POS]):
                item_types = self.accept(e.args[0])
                for item_type in item_types:
                    new_type = self.chk.named_generic_type(typename, [item_type])
                    new_types.append(new_type)
                    self.add_infer_type((node, new_type), [(node, partial_type), (e.args[0], item_type)], self_infer=True)
            elif (typename in self.container_args
                and methodname in self.container_args[typename]
                and e.arg_kinds == [ARG_POS]):
                arg_types = get_proper_type(self.accept(e.args[0]))
                for arg_type in arg_types:
                    if isinstance(arg_type, Instance):
                        arg_typename = arg_type.type.fullname
                        if arg_typename in self.container_args[typename][methodname]:
                            new_type = self.chk.named_generic_type(typename,
                                                                list(arg_type.args))
                            new_types.append(new_type)
                            self.add_infer_type((node, new_type), [(node, partial_type), (e.args[0], arg_type)], self_infer=True)
                        else:
                            new_type = partial_type
                            new_types.append(new_type)
                    elif isinstance(arg_type, AnyType):
                        new_type = self.chk.named_type(typename)
                        new_types.append(new_type)
                        self.add_infer_type((node, new_type), [(node, partial_type), (e.args[0], arg_type)], self_infer=True)
        self.chk.store_type(node, new_types, overwrite=True )
        return new_types
    def check_call_expr_with_callee_type(self,
                                         callee_type: Type,
                                         e: CallExpr,
                                         callable_name: Optional[str],
                                         object_type: Optional[Type],
                                         member: Optional[str] = None, reason = None, infer_type = None, corrects = None, rejects = None) -> Set[Type]:
        if callable_name is None and member is not None:
            assert object_type is not None
            callable_name = self.method_fullname(object_type, member)
        object_type = get_proper_type(object_type)
        return self.check_call(callee_type, e.args, e.arg_kinds, e,
                               e.arg_names, callable_node=e.callee,
                               callable_name=callable_name,
                               object_type=object_type, corrects = corrects, method_node=e.callee, rejects = rejects)[0]
    def check_union_call_expr(self, e: CallExpr, object_type: UnionType, member: str, reason = None, infer_type = None) -> Set[Type]:
        res: List[Type] = []
        for typ in object_type.relevant_items():
            with self.msg.disable_errors():
                item = analyze_member_access(member, typ, e, False, False, False,
                                             self.msg, original_type=object_type, chk=self.chk,
                                             in_literal_context=self.is_literal_context(),
                                             self_type=typ)
            narrowed = self.narrow_type_from_binder(e.callee, item, skip_non_overlapping=True)
            if narrowed is None:
                continue
            callable_name = self.method_fullname(typ, member)
            item_object_type = typ if callable_name else None
            ret = self.check_call_expr_with_callee_type(narrowed, e, callable_name,
                                                             item_object_type)
            res.append(ret)
        return make_simplified_union(res)
    def check_call(self,
                   callee: Type,
                   args: List[Expression],
                   arg_kinds: List[ArgKind],
                   context: Context,
                   arg_names: Optional[Sequence[Optional[str]]] = None,
                   callable_node: Optional[Expression] = None,
                   arg_messages: Optional[MessageBuilder] = None,
                   callable_name: Optional[str] = None,
                   object_type: Optional[Type] = None, corrects = None, rejects = None, method_node = None) -> Tuple[Type, Type]:
        arg_messages = arg_messages or self.msg  
        callee = get_proper_type(callee)
        if isinstance(callee, CallableType):
            if callee.is_generic():
                ret =  self.check_generic_call(callee, args, arg_kinds, context, arg_names,
                                                callable_node, arg_messages, callable_name,
                                                object_type, corrects=corrects, rejects = rejects, method_node=method_node)
                return ret
            else:
                ret =  self.check_callable_call(callee, args, arg_kinds, context, arg_names,
                                                callable_node, arg_messages, callable_name,
                                                object_type, corrects=corrects, rejects = rejects, method_node=method_node)
                return ret
        elif isinstance(callee, Overloaded):
            return self.check_overload_call(callee, args, arg_kinds, arg_names, callable_name,
                                            object_type, context, arg_messages, corrects = corrects, rejects=rejects, method_node=method_node)
        elif isinstance(callee, AnyType):
            return self.check_any_type_call(args, callee)
        elif isinstance(callee, UnionType):
            rets = []
            self.chk.union_context = callee
            for c in callee.items:
                if isinstance(c, CallableType):
                    if c.is_generic():
                        ret, _ =  self.check_generic_call(c, args, arg_kinds, context, arg_names,
                                                        callable_node, arg_messages, callable_name,
                                                        object_type, corrects=corrects, rejects = rejects, method_node=method_node)
                        return ret
                    else:
                        ret, _ = self.check_callable_call(c, args, arg_kinds, context, arg_names,
                                                    callable_node, arg_messages, callable_name,
                                                    object_type, corrects=corrects, rejects = rejects, method_node=method_node)
                    rets.extend(ret)
            self.chk.union_context = None
            return rets, AnyType(TypeOfAny.special_form)
        elif isinstance(callee, Instance):
            call_function = analyze_member_access('__call__', callee, context, is_lvalue=False,
                                                  is_super=False, is_operator=True, msg=self.msg,
                                                  original_type=callee, chk=self.chk,
                                                  in_literal_context=self.is_literal_context(), object_node = callable_node)
            callable_name = callee.type.fullname + ".__call__"
            result = self.check_call(call_function, args, arg_kinds, context, arg_names,
                                     callable_node, arg_messages, callable_name, callee, corrects = corrects)
            if callable_node:
                self.chk.store_type(callable_node, [callee])
            return result
        elif isinstance(callee, TypeVarType):
            self.add_infer_type((callable_node, callee.upper_bound,), [(callable_node, callee)], self_infer=True)
            return self.check_call(callee.upper_bound, args, arg_kinds, context, arg_names,
                                   callable_node, arg_messages)
        elif isinstance(callee, TypeType):
            item = self.analyze_type_type_callee(callee.item, context)
            return self.check_call(item, args, arg_kinds, context, arg_names,
                                   callable_node, arg_messages, corrects=corrects, rejects=rejects)
        elif isinstance(callee, TupleType):
            return self.check_call(tuple_fallback(callee), args, arg_kinds, context,
                                   arg_names, callable_node, arg_messages, callable_name,
                                   object_type)
        else:
            return {AnyType(TypeOfAny.from_error)}, AnyType(TypeOfAny.from_error) 
    def check_generic_call(self,
                            callee: CallableType,
                            args: List[Expression],
                            arg_kinds: List[ArgKind],
                            context: Context,
                            arg_names: Optional[Sequence[Optional[str]]],
                            callable_node: Optional[Expression],
                            arg_messages: MessageBuilder,
                            callable_name: Optional[str],
                            object_type: Optional[Type], formal2node = None, corrects = None, rejects = None, method_node = None) -> Tuple[Type, Type]:
        if callable_name is None and callee.name:
            callable_name = callee.name
        ret_type = callee.ret_type
        if callee.is_type_obj() and isinstance(ret_type, Instance):
            callable_name = ret_type.type.fullname
        formal_to_actual = map_actuals_to_formals(
            arg_kinds, arg_names,
            callee.arg_kinds, callee.arg_names,
            lambda i: self.accept(args[i]))
        generic_indices = set()
        for i, actuals in enumerate(formal_to_actual):
            if is_generic(callee.arg_types[i]):
                generic_indices.update(actuals)
        arg_types = self.infer_arg_types_in_context(
                    callee, args, arg_kinds, formal_to_actual)
        def expand(l):
            x = []
            for ll in l:
                if isinstance(ll, list):
                    x.extend(ll)
                else:
                    x.append(ll)
            return x
        generic_types = [arg_types[x] for x in generic_indices] 
        generic_args = [args[x] for x in generic_indices]
        GA = itertools.product(*generic_types)
        original_generic_indices = self.generic_indices 
        original_generic_arg_types = self.generic_arg_types
        self.generic_indices = generic_indices
        rejects_tv = defaultdict(list)
        rejects_k = []
        rets = []
        examized_combinations = 0
        for ga in GA:
            examized_combinations += 1
            if examized_combinations > self.chk.combination_limits:
                break
            ga_extended = []
            j = 0
            for i in range(len(arg_types)):
                if i in generic_indices:
                    ga_extended.append(ga[j])
                    j += 1
                else:
                    ga_extended.append('phi')
            self.generic_arg_types = ga_extended
            cs = constraints.infer_constraints_for_generic_arguments(callee, ga_extended, arg_kinds, formal_to_actual)
            type_vars = callee.type_var_ids()
            best = solve_constraints(type_vars, cs, True, maybe=False)
            new_callee = self.apply_generic_arguments(callee, best, context, skip_unsatisfied=True, fail=True)
            partial_corrects = []
            partial_rejects = []
            if new_callee is None:
                for i, actuals in enumerate(formal_to_actual): 
                    for actual in actuals:
                        actual_type = arg_types[actual]
                        if self.generic_indices is not None and actual in self.generic_indices:
                            actual_type = {self.generic_arg_types[actual]}
                        for at in actual_type:
                            partial_rejects.append((args[actual], at))
                ret = {AnyType(0)}
            else:
                ret, _ = self.check_call(
                callee=new_callee,
                args=args,
                arg_kinds=arg_kinds,
                arg_names=arg_names,
                context=context,
                callable_name=callable_name,
                object_type=object_type, corrects=partial_corrects, rejects = partial_rejects, method_node = method_node)
            if callee == new_callee and len(generic_indices) > 0:
                self.generic_indices = original_generic_indices 
                self.generic_arg_types = original_generic_arg_types 
                return {AnyType(0)}, callee
            rets.extend(ret)
            ok_args = list(itertools.product(*partial_corrects))
            for ok_arg in ok_args:
                ok_arg = [x[1] for x in ok_arg]
                if len(ok_arg) > 0:
                    if corrects is not None:
                        corrects.append((tuple(zip(args, ok_arg)), new_callee.ret_type))
            for i, g in enumerate(ga):
                a = generic_args[i]
                rejects_tv[(a, g)].append(partial_rejects)
            rejects_k.append(partial_rejects)
        for ag in rejects_tv:
            a, g = ag
            if all(ag in x for x in rejects_tv[ag]):
                if rejects is not None:
                    rejects.append(ag)
                else:
                    self.add_incompatible(a, g, method_node, callee)
        reject_pairs = []
        for l in rejects_k:
            reject_pairs.extend(l)
        reject_pairs = set(reject_pairs)
        for reject_pair in reject_pairs:
            if reject_pair[0] in generic_args:
                continue
            if all([reject_pair in x for x in rejects_k]):
                if rejects is not None:
                    rejects.append((reject_pair[0], reject_pair[1]))
                else:
                    self.add_incompatible(reject_pair[0], reject_pair[1], method_node, callee)
        self.generic_indices = original_generic_indices 
        self.generic_arg_types = original_generic_arg_types 
        if len(rets) > 0:
            return rets, callee
        else:
            return [AnyType(0)], callee
    def put_into_correct_level(self, func, argument, at):
        self.chk.func_candidates[func][argument].add(at)
        self.chk.func_must[func][argument].add(at)
        if isinstance(at, Instance):
            t = (at.type, at.args)
            if at.type.fullname == 'builtins.list' or at.type.fullname == 'builtins.set' or at.type.fullname == 'builtins.dict':
                self.chk.func_s3[func][argument].add(at)
            else:
                self.chk.func_s2[func][argument].add(at)
        elif isinstance(at, CallableType):
            self.chk.func_s3[func][argument].add(at)
        elif not isinstance(at, AnyType) and not isinstance(at, NoneType) and not isinstance(at, PartialType) and not isinstance(at, UnionType) and not isinstance(at, TypeVarType) and not isinstance(at, CallableType) and not isinstance(at, UninhabitedType):
            self.chk.func_s3[func][argument].add(at)
    def check_argument_analyzed(self, func, arg_types, formal_to_actual):
        analyzed = True
        nows = self.chk.func_finished[func]
        for i, actuals in enumerate(formal_to_actual): 
            is_method = bool(func.info) and not func.is_static
            if i+int(is_method) >= len(func.arguments):
                break
            argument = func.arguments[i+int(is_method)]
            candidates = nows[argument]
            for actual in actuals:
                actual_type = arg_types[actual]
                actual_types = actual_type
                for at in actual_types:
                    if isinstance(at, Instance):
                        t = (at.type, at.args)
                        if at.type.fullname == 'builtins.list' or at.type.fullname == 'builtins.set' or at.type.fullname == 'builtins.dict':
                            if any(isinstance(x, TypeVarType) for x in at.args):
                                continue
                        if at.type.fullname == 'builtins.bool':
                            continue
                        if at not in candidates and t not in candidates:
                            analyzed = False
                            self.chk.put_into_correct_level(func, argument, at)
                    elif isinstance(at, CallableType):
                        if at not in candidates:
                            analyzed = False
                            self.chk.put_into_correct_level(func, argument, at)
                    elif isinstance(at, TupleType) and at.partial_fallback is not None:
                        at = at.partial_fallback
                        if at not in candidates:
                            analyzed = False
                            self.chk.put_into_correct_level(func, argument, at)
                    elif not isinstance(at, AnyType) and not isinstance(at, NoneType) and not isinstance(at, PartialType) and not isinstance(at, UnionType) and not isinstance(at, TypeVarType) and not isinstance(at, CallableType) and not isinstance(at, UninhabitedType):
                        if at not in candidates:
                            analyzed = False
                            self.chk.put_into_correct_level(func, argument, at)
        return analyzed
    def check_callable_call(self,
                            callee: CallableType,
                            args: List[Expression],
                            arg_kinds: List[ArgKind],
                            context: Context,
                            arg_names: Optional[Sequence[Optional[str]]],
                            callable_node: Optional[Expression],
                            arg_messages: MessageBuilder,
                            callable_name: Optional[str],
                            object_type: Optional[Type], formal2node = None, corrects = None, rejects = None, method_node = None) -> Tuple[Type, Type]:
        if callable_name is None and callee.name:
            callable_name = callee.name
        ret_type = callee.ret_type
        if callee.is_type_obj() and isinstance(ret_type, Instance):
            callable_name = ret_type.type.fullname
        formal_to_actual = map_actuals_to_formals(
            arg_kinds, arg_names,
            callee.arg_kinds, callee.arg_names,
            lambda i: self.accept(args[i]))
        arg_types = self.infer_arg_types_in_context(
            callee, args, arg_kinds, formal_to_actual)
        ok = self.check_argument_count(callee, arg_types, arg_kinds,
                                  arg_names, formal_to_actual, context, self.msg, object_type)
        if self.chk.mode != 'CPA' and hasattr(method_node, "node"):
            if isinstance(method_node.node, list):
                for md in method_node.node:
                    if md in self.chk.func_candidates:
                        analyzed = self.check_argument_analyzed(md, arg_types, formal_to_actual)
                        if not analyzed:
                            self.chk.defer_node(md, self.chk.func_class[md])
                            self.chk.handle_cannot_determine_type('', context)   
            elif method_node.node in self.chk.func_candidates:
                analyzed = self.check_argument_analyzed(method_node.node, arg_types, formal_to_actual)
                if not analyzed:
                    self.chk.defer_node(method_node.node, self.chk.func_class[method_node.node])
                    self.chk.handle_cannot_determine_type('', context)
            elif isinstance(method_node.node, TypeInfo) and method_node.node.get('__init__').node in self.chk.func_candidates:
                mnode = method_node.node.get('__init__').node
                analyzed = self.check_argument_analyzed(mnode, arg_types, formal_to_actual)
                if not analyzed:
                    self.chk.defer_node(mnode, self.chk.func_class[mnode])
                    self.chk.handle_cannot_determine_type('', context)
            else:
                analyzed = True
        if ok:
            self.check_argument_types(arg_types, arg_kinds, args, callee, formal_to_actual, context,
                                  messages=arg_messages, object_type=object_type, formal2node=formal2node, callable_name = callable_name, corrects = corrects, rejects = rejects,
                                  method_node=method_node)
        if callable_node:
            self.chk.store_type(callable_node, [callee])
        return {callee.ret_type}, callee
    def analyze_type_type_callee(self, item: ProperType, context: Context) -> Set[Type]:
        """Analyze the callee X in X(...) where X is Type[item].
        i.e. X is an abstract class for a item
        Return a Y that we can pass to check_call(Y, ...).
        """
        if isinstance(item, AnyType):
            return AnyType(TypeOfAny.from_another_any, source_any=item)
        if isinstance(item, Instance):
            res = type_object_type(item.type, self.named_type)
            if isinstance(res, CallableType):
                res = res.copy_modified(from_type_type=True)
            expanded = get_proper_type(expand_type_by_instance(res, item))
            if isinstance(expanded, CallableType):
                expanded = expanded.copy_modified(variables=[])
            return expanded
        if isinstance(item, UnionType):
            return UnionType([self.analyze_type_type_callee(get_proper_type(tp), context)
                              for tp in item.relevant_items()], item.line)
        if isinstance(item, TypeVarType):
            callee = self.analyze_type_type_callee(get_proper_type(item.upper_bound), context)
            callee = get_proper_type(callee)
            if isinstance(callee, CallableType):
                callee = callee.copy_modified(ret_type=item)
            elif isinstance(callee, Overloaded):
                callee = Overloaded([c.copy_modified(ret_type=item)
                                     for c in callee.items])
            return callee
        if (isinstance(item, TupleType)
                and tuple_fallback(item).type.fullname != 'builtins.tuple'):
            return self.analyze_type_type_callee(tuple_fallback(item), context)
        self.msg.unsupported_type_type(item, context) 
        return AnyType(TypeOfAny.from_error)
    def infer_arg_types_in_empty_context(self, args: List[Expression]) -> List[Type]:
        """Infer argument expression types in an empty context.
        In short, we basically recurse on each argument without considering
        in what context the argument was called.
        """
        res: List[Type] = []
        for arg in args:
            arg_type = self.accept(arg)
            res.append(arg_type)
        return res
    def infer_arg_types_in_context(
            self, callee: CallableType, args: List[Expression], arg_kinds: List[ArgKind],
            formal_to_actual: List[List[int]]) -> List[Type]:
        """Infer argument expression types using a callable type as context.
        For example, if callee argument 2 has type List[int], infer the
        argument expression with List[int] type context.
        Returns the inferred types of *actual arguments*.
        """
        res: List[Optional[Type]] = [None] * len(args)
        for i, actuals in enumerate(formal_to_actual):
            for ai in actuals:
                if not arg_kinds[ai].is_star():
                    res[ai] = self.accept(args[ai], callee.arg_types[i])
        for i, t in enumerate(res):
            if not t:
                res[i] = self.accept(args[i])
        assert all(tp is not None for tp in res)
        return cast(List[Type], res)
    def check_argument_count(self,
                             callee: CallableType,
                             actual_types: List[Type],
                             actual_kinds: List[ArgKind],
                             actual_names: Optional[Sequence[Optional[str]]],
                             formal_to_actual: List[List[int]],
                             context: Optional[Context],
                             messages: Optional[MessageBuilder], object_type=None) -> bool:
        """Check that there is a value for all required arguments to a function.
        Also check that there are no duplicate values for arguments. Report found errors
        using 'messages' if it's not None. If 'messages' is given, 'context' must also be given.
        Return False if there were any errors. Otherwise return True
        """
        if messages:
            assert context, "Internal error: messages given without context"
        elif context is None:
            context = TempNode(AnyType(TypeOfAny.special_form))
        all_actuals: List[int] = []
        for actuals in formal_to_actual:
            all_actuals.extend(actuals)
        ok, is_unexpected_arg_error = self.check_for_extra_actual_arguments(
            callee, actual_types, actual_kinds, actual_names, all_actuals, context, messages)
        for i, kind in enumerate(callee.arg_kinds):
            if kind.is_required() and not formal_to_actual[i] and not is_unexpected_arg_error:
                if messages:
                    if kind.is_positional():
                        messages.too_few_arguments(callee, context, actual_names)
                    else:
                        argname = callee.arg_names[i] or "?"
                        messages.missing_named_argument(callee, context, argname)
                ok = False
            elif not kind.is_star() and is_duplicate_mapping(
                    formal_to_actual[i], actual_types, actual_kinds):
                    ok = False
            elif (kind.is_named() and formal_to_actual[i] and
                  actual_kinds[formal_to_actual[i][0]] not in [nodes.ARG_NAMED, nodes.ARG_STAR2]):
                if messages:
                    messages.too_many_positional_arguments(callee, context)
                ok = False
        if not ok:
            if isinstance(context, CallExpr):
                self.add_single_incompatible(context.callee, callee)
        return ok
    def check_for_extra_actual_arguments(self,
                                         callee: CallableType,
                                         actual_types: List[Type],
                                         actual_kinds: List[ArgKind],
                                         actual_names: Optional[Sequence[Optional[str]]],
                                         all_actuals: List[int],
                                         context: Context,
                                         messages: Optional[MessageBuilder]) -> Tuple[bool, bool]:
        """Check for extra actual arguments.
        Return tuple (was everything ok,
                      was there an extra keyword argument error [used to avoid duplicate errors]).
        """
        is_unexpected_arg_error = False  
        ok = True  
        for i, kind in enumerate(actual_kinds):
            if (i not in all_actuals and
                    (kind != nodes.ARG_STAR or is_non_empty_tuple(actual_types[i])) and
                    kind != nodes.ARG_STAR2):
                ok = False
                if kind != nodes.ARG_NAMED:
                    if messages:
                        messages.too_many_arguments(callee, context)
                else:
                    if messages:
                        assert actual_names, "Internal error: named kinds without names given"
                        act_name = actual_names[i]
                        assert act_name is not None
                        act_type = actual_types[i]
                    is_unexpected_arg_error = True
            elif ((kind == nodes.ARG_STAR and nodes.ARG_STAR not in callee.arg_kinds)
                  or kind == nodes.ARG_STAR2):
                actual_type = get_proper_type(actual_types[i])
                if isinstance(actual_type, (TupleType, TypedDictType)):
                    if all_actuals.count(i) < len(actual_type.items):
                        if messages:
                            if (kind != nodes.ARG_STAR2
                                    or not isinstance(actual_type, TypedDictType)):
                                messages.too_many_arguments(callee, context)
                            else:
                                messages.too_many_arguments_from_typed_dict(callee, actual_type,
                                                                            context)
                                is_unexpected_arg_error = True
                        ok = False
        return ok, is_unexpected_arg_error
    def check_argument_types(self,
                             arg_types: List[Type],
                             arg_kinds: List[ArgKind],
                             args: List[Expression],
                             callee: CallableType,
                             formal_to_actual: List[List[int]],
                             context: Context,
                             messages: Optional[MessageBuilder] = None,
                             check_arg: Optional[ArgChecker] = None,
                             object_type: Optional[Type] = None, 
                             formal2node = None, callable_name = None, 
                             corrects = None, rejects = None,
                             method_node = None) -> None:
        messages = messages or self.msg
        check_arg = check_arg or self.check_arg
        mapper = ArgTypeExpander()
        options = []
        need_to_check = sum([len(x) for x in formal_to_actual])
        if need_to_check == 0 and corrects is not None:
            corrects.append(tuple([(0, 0, 1)]))
        for i, actuals in enumerate(formal_to_actual): 
            for actual in actuals:
                actual_type = arg_types[actual]
                if self.generic_indices is not None and actual in self.generic_indices:
                    actual_type = {self.generic_arg_types[actual]}
                if actual_type is None:
                    continue  
                expanded_actual = actual_type
                correct = set()
                check_arg(expanded_actual, actual_type, arg_kinds[actual],
                          callee.arg_types[i],
                          actual + 1, i + 1, callee, object_type, args[actual], context, messages, callable_name = callable_name, correct = correct, rejects = rejects, method_node=method_node)
                if corrects is not None:            
                    corrects.append(tuple(correct))
    def check_arg(self,
                  caller_type: Type,
                  original_caller_type: Type,
                  caller_kind: ArgKind,
                  callee_type: Type,
                  n: int,
                  m: int,
                  callee: CallableType,
                  object_type: Optional[Type],
                  context: Context,
                  outer_context: Context,
                  messages: MessageBuilder, callable_name = None, correct = None, rejects = None, method_node = None) -> None:
        """Check the type of a single argument in a call."""
        caller_type = get_proper_type(caller_type)
        original_caller_type = get_proper_type(original_caller_type)
        callee_type = get_proper_type(callee_type)
        if isinstance(caller_type, DeletedType):
            return {AnyType(0)}
        else:
            if object_type is None:
                object_type = callee
            res = False
            start = time.time()
            for item in caller_type:
                res = is_subtype(item, callee_type)
                rejected = context
                if not res:
                    if rejects is not None:
                        rejects.append((rejected, item))
                    else:
                        if method_node is not None:
                            self.add_improvement_from_pair(rejected, item)
                            if self.chk.union_context:
                                self.add_incompatible(rejected, item, method_node, self.chk.union_context)
                            else:
                                self.add_incompatible(rejected, item, method_node, callee)
                else:
                    if item == callee_type: 
                        correct.add((context, item, 1))
                    else:
                        correct.add((context, item, 0.5))
            return res
    def check_overload_call(self,
                            callee: Overloaded,
                            args: List[Expression],
                            arg_kinds: List[ArgKind],
                            arg_names: Optional[Sequence[Optional[str]]],
                            callable_name: Optional[str],
                            object_type: Optional[Type],
                            context: Context,
                            arg_messages: MessageBuilder, corrects = None, rejects = None, method_node = None, plausible_targets = None, corrects_k_tv=None, rejects_k_tv=None) -> Tuple[Type, Type]:
        def merge_corrects_k(corrects_now, corrects_tv):
            for idx in corrects_tv:
                corrects_now[idx] = corrects_tv[idx]
            return corrects_now
        arg_types = self.infer_arg_types_in_empty_context(args)
        from_generic = plausible_targets is not None
        if plausible_targets is None:
            plausible_targets = self.plausible_overload_call_targets(arg_types, arg_kinds,
                                                                 arg_names, callee)
        if len(plausible_targets) == 0:
            for arg, arg_types in zip(args, arg_types):
                for arg_type in arg_types:
                    if rejects is None:
                        self.add_single_incompatible(method_node, callee)
                        break
                    else:
                        rejects.append((arg, arg_type))
        corrects_k = {} 
        rejects_k = {} 
        self.infer_overload_return_type(plausible_targets, args, arg_types,
                                                          arg_kinds, arg_names, callable_name,
                                                          object_type, context, arg_messages, corrects_k = corrects_k, rejects_k = rejects_k, method_node = method_node)
        rets = []
        if len(args) == 0:
            rets = [x.ret_type for x in plausible_targets]
            if corrects is not None:
                for x in sorted(plausible_targets, key=lambda x:str(x)):
                    if not isinstance(x.ret_type, AnyType):
                        corrects.append((0, x.ret_type))
                        break
        else:
            record = {}
            for k in corrects_k:
                corrects_now = corrects_k[k]
                if corrects_k_tv is not None:
                    corrects_now = merge_corrects_k(corrects_now, corrects_k_tv[k])
                cl = list(corrects_now)
                if len(corrects_now) > 0 and len(cl[0]) > 0:
                    if len(cl[0][0]) == 3 and (len(cl[0]) == 1 or isinstance(cl[0][1], Tuple)):
                        choices = itertools.product(*corrects_now)
                        for i, choice in enumerate(choices):
                            if i > self.chk.combination_limits:
                                break
                            score = sum([x[2] for x in choice])
                            args = tuple([(x[0], x[1]) for x in choice])
                            args = tuple(sorted(args, key=lambda x:str(x[0])))
                            if args in record:
                                old_score, _ = record[args]
                                if old_score < score:
                                    record[args] = (score, k.ret_type)
                            else:
                                record[args] = (score, k.ret_type)
                    else:
                        for c in corrects_now:
                            args = tuple(c[0])
                            ret = c[1]
                            record[args] = (0, ret)
            for args in record:
                ret = record[args][1]
                if not isinstance(ret, AnyType) and corrects is not None:
                    corrects.append((args, ret))
                    rets.append(ret)
            for k in rejects_k:
                rejects_now = rejects_k[k]
                if corrects_k_tv is not None:
                    rejects_k[k] = merge_corrects_k(rejects_now, rejects_k_tv[k])
        def expand(l):
            x = []
            for ll in l:
                if isinstance(ll, list):
                    x.extend(ll)
                else:
                    x.append(ll)
            return x
        reject_pairs = []
        rejects_k = {k:expand(v) for k, v in rejects_k.items()}
        for l in rejects_k.values():
            reject_pairs.extend(l)
        reject_pairs = set(reject_pairs)
        for reject_pair in reject_pairs:
            if all([reject_pair in rejects_k[k] for k in rejects_k]):
                if rejects is not None:
                    rejects.append((reject_pair[0], reject_pair[1]))
                else:
                    self.add_incompatible(reject_pair[0], reject_pair[1], method_node, callee)
        if len(rets) > 0:
            return rets, callee
        else:
            return {AnyType(0)}, callee
    def plausible_overload_call_targets(self,
                                        arg_types: List[Type],
                                        arg_kinds: List[ArgKind],
                                        arg_names: Optional[Sequence[Optional[str]]],
                                        overload: Overloaded) -> List[CallableType]:
        def has_shape(typ: Type) -> bool:
            typ = get_proper_type(typ)
            return (isinstance(typ, TupleType) or isinstance(typ, TypedDictType)
                    or (isinstance(typ, Instance) and typ.type.is_named_tuple))
        matches: List[CallableType] = []
        star_matches: List[CallableType] = []
        args_have_var_arg = False
        args_have_kw_arg = False
        for kind, typ in zip(arg_kinds, arg_types):
            if kind == ARG_STAR and not has_shape(typ):
                args_have_var_arg = True
            if kind == ARG_STAR2 and not has_shape(typ):
                args_have_kw_arg = True
        for typ in overload.items:
            formal_to_actual = map_actuals_to_formals(arg_kinds, arg_names,
                                                      typ.arg_kinds, typ.arg_names,
                                                      lambda i: arg_types[i])
            if self.check_argument_count(typ, arg_types, arg_kinds, arg_names,
                                         formal_to_actual, None, None):
                if args_have_var_arg and typ.is_var_arg:
                    star_matches.append(typ)
                elif args_have_kw_arg and typ.is_kw_arg:
                    star_matches.append(typ)
                else:
                    matches.append(typ)
        return star_matches + matches
    def infer_overload_return_type(self,
                                   plausible_targets: List[CallableType],
                                   args: List[Expression],
                                   arg_types: List[Type],
                                   arg_kinds: List[ArgKind],
                                   arg_names: Optional[Sequence[Optional[str]]],
                                   callable_name: Optional[str],
                                   object_type: Optional[Type],
                                   context: Context,
                                   arg_messages: Optional[MessageBuilder] = None,
                                   corrects_k = None,
                                   rejects_k = None,
                                   method_node = None
                                   ) -> Optional[Tuple[Type, Type]]:
        arg_messages = self.msg if arg_messages is None else arg_messages
        for typ in plausible_targets:
            overload_messages = self.msg.clean_copy()
            prev_messages = self.msg
            assert self.msg is self.chk.msg
            self.msg = overload_messages
            self.chk.msg = overload_messages
            corrects = []
            rejects = []
            ret_type, infer_type = self.check_call(
                callee=typ,
                args=args,
                arg_kinds=arg_kinds,
                arg_names=arg_names,
                context=context,
                arg_messages=overload_messages,
                callable_name=callable_name,
                object_type=object_type, corrects=corrects, rejects = rejects, method_node = method_node)
            corrects_k[infer_type] = corrects
            rejects_k[infer_type] = rejects
        return None
    def apply_generic_arguments(self, callable: CallableType, types: Sequence[Optional[Type]],
                                context: Context, skip_unsatisfied: bool = False, fail=False) -> CallableType:
        """Simple wrapper around mypy.applytype.apply_generic_arguments."""
        return applytype.apply_generic_arguments(callable, types,
                                                 self.msg.incompatible_typevar_value, context,
                                                 skip_unsatisfied=skip_unsatisfied, fail=fail)
    def check_any_type_call(self, args: List[Expression], callee: Type) -> Tuple[Type, Type]:
        self.infer_arg_types_in_empty_context(args)
        callee = get_proper_type(callee)
        if isinstance(callee, AnyType):
            return ({AnyType(TypeOfAny.from_another_any, source_any=callee)},
                    AnyType(TypeOfAny.from_another_any, source_any=callee))
        else:
            return {AnyType(TypeOfAny.special_form)}, AnyType(TypeOfAny.special_form)
    def check_union_call(self,
                         callee: UnionType,
                         args: List[Expression],
                         arg_kinds: List[ArgKind],
                         arg_names: Optional[Sequence[Optional[str]]],
                         context: Context,
                         arg_messages: MessageBuilder, callable_name = None, correct=None, reject=None) -> Tuple[Type, Type]:
        self.msg.disable_type_names += 1
        results = [self.check_call(subtype, args, arg_kinds, context, arg_names,
                                   arg_messages=arg_messages, callable_name = callable_name)
                   for subtype in callee.relevant_items()]
        self.msg.disable_type_names -= 1
        mu_type = []
        for res in results:
            if res[0] not in mu_type:
                mu_type.append(res[0])
        return (UnionType.make_union(mu_type), callee)        
    def visit_member_expr(self, e: MemberExpr, is_lvalue: bool = False) -> Set[Type]:
        """Visit member expression (of form e.id)."""
        self.chk.module_refs.update(extract_refexpr_names(e))
        result = self.analyze_ordinary_member_access(e, is_lvalue)
        return self.narrow_type_from_binder(e, result)
    def analyze_ordinary_member_access(self, e: MemberExpr,
                                       is_lvalue: bool, temp_rhs = None) -> Set[Type]:
        """Analyse member expression or member lvalue."""
        if e.kind is not None:
            return self.analyze_ref_expr(e)
        else:
            original_types = self.accept(e.expr)
            name = e.name
            ret = []
            for original_type in original_types:
                base = e.expr
                module_symbol_table = None
                if isinstance(base, RefExpr) and isinstance(base.node, MypyFile):
                    module_symbol_table = base.node.names
                member_type = analyze_member_access(
                    e.name, original_type, e, is_lvalue, False, False,
                    self.msg, original_type=original_type, chk=self.chk,
                    in_literal_context=self.is_literal_context(),
                    module_symbol_table=module_symbol_table, object_node=e.expr, member_expr=e)
                if not isinstance(member_type, AnyType):
                    self.add_infer_type((e, member_type), [(e.expr, original_type)])
                else:
                    self.add_infer_type((e, member_type), [(e.expr, original_type)], node_only=True)  
                ret.append(member_type)
            if len(ret) == 0:
                return [AnyType(TypeOfAny.from_error)]
            else:
                return ret
    def is_literal_context(self) -> bool:
        return is_literal_type_like(self.type_context[-1])
    def infer_literal_expr_type(self, value: LiteralValue, fallback_name: str) -> Set[Type]:
        typ = self.named_type(fallback_name)
        return typ
    def concat_tuples(self, left: TupleType, right: TupleType) -> TupleType:
        return TupleType(items=left.items + right.items,
                         fallback=self.named_type('builtins.tuple'))
    def visit_int_expr(self, e: IntExpr) -> Set[Type]:
        int_type =  self.infer_literal_expr_type(e.value, 'builtins.int')
        self.add_infer_type((e, int_type), [])
        return int_type
    def visit_str_expr(self, e: StrExpr) -> Set[Type]:
        str_type =  self.infer_literal_expr_type(e.value, 'builtins.str')
        self.add_infer_type((e, str_type), [])
        return str_type
    def visit_bytes_expr(self, e: BytesExpr) -> Set[Type]:
        return self.infer_literal_expr_type(e.value, 'builtins.bytes')
    def visit_unicode_expr(self, e: UnicodeExpr) -> Set[Type]:
        return self.infer_literal_expr_type(e.value, 'builtins.unicode')
    def visit_float_expr(self, e: FloatExpr) -> Set[Type]:
        float_type = self.named_type('builtins.float')
        self.add_infer_type((e, float_type), [])
        return float_type
    def visit_complex_expr(self, e: ComplexExpr) -> Set[Type]:
        return self.named_type('builtins.complex')
    def visit_ellipsis(self, e: EllipsisExpr) -> Set[Type]:
        if self.chk.options.python_version[0] >= 3:
            return self.named_type('builtins.ellipsis')
        else:
            return self.named_type('builtins.object')
    def visit_op_expr(self, e: OpExpr) -> Set[Type]:
        if e.op == 'and' or e.op == 'or':
            return self.check_boolean_op(e, e)
        if e.op == '*' and isinstance(e.left, ListExpr):
            return self.check_list_multiply(e)
        if e.op == '%':
            pyversion = self.chk.options.python_version
            if pyversion[0] == 3:
                if isinstance(e.left, BytesExpr) and pyversion[1] >= 5:
                    return self.strfrm_checker.check_str_interpolation(e.left, e.right)
                if isinstance(e.left, StrExpr):
                    return self.strfrm_checker.check_str_interpolation(e.left, e.right)
            elif pyversion[0] <= 2:
                if isinstance(e.left, (StrExpr, BytesExpr, UnicodeExpr)):
                    return self.strfrm_checker.check_str_interpolation(e.left, e.right)
        left_type = self.accept(e.left)
        proper_left_type = get_proper_type(left_type)
        if isinstance(proper_left_type, TupleType) and e.op == '+':
            left_add_method = proper_left_type.partial_fallback.type.get('__add__')
            if left_add_method and left_add_method.fullname == 'builtins.tuple.__add__':
                proper_right_type = get_proper_type(self.accept(e.right))
                if isinstance(proper_right_type, TupleType):
                    right_radd_method = proper_right_type.partial_fallback.type.get('__radd__')
                    if right_radd_method is None:           
                        return {self.concat_tuples(proper_left_type, proper_right_type)}
        if e.op in operators.op_methods:    
            method = self.get_operator_method(e.op)
            method_node = self.get_temp_nodes(method, e)   
            result, method_type = self.check_op(method, left_type, e.right, e,
                                                allow_reverse=True, object_node = e.left, method_node=method_node, return_node=e)
            e.method_type = method_type
            return result
        else:
            raise RuntimeError('Unknown operator {}'.format(e.op))
    def visit_comparison_expr(self, e: ComparisonExpr) -> Set[Type]:
        result: Optional[Type] = None
        sub_result: Optional[Type] = None
        for left, right, operator in zip(e.operands, e.operands[1:], e.operators):
            left_type = self.accept(left)
            method_type: Optional[extyper.types.Type] = None
            if operator == 'in' or operator == 'not in':
                right_type = self.accept(right)  
                method_node = self.get_temp_nodes(AnyType(0), e)
                _, method_type = self.check_method_call_by_name(
                    '__contains__', right_type, [left], [ARG_POS], e, object_node=right, method_node=method_node, return_node=e)
                sub_result = self.bool_type()
            elif operator in operators.op_methods:
                method = self.get_operator_method(operator)
                method_node = self.get_temp_nodes(method, e)
                sub_result, method_type = self.check_op(method, left_type, right, e,
                                                        allow_reverse=True, object_node=left, method_node=method_node, return_node = e)
            elif operator == 'is' or operator == 'is not':
                right_type = self.accept(right)  
                sub_result = self.bool_type()
                method_type = None
            else:
                raise RuntimeError('Unknown comparison operator {}'.format(operator))
            e.method_types.append(method_type)
            if result is None:
                result = sub_result
            else:
                result = join.join_types(result, sub_result)
        assert result is not None
        return result
    def get_operator_method(self, op: str) -> str:
        if op == '/' and self.chk.options.python_version[0] == 2:
            return '__div__'
        else:
            return operators.op_methods[op]
    def check_method_call_by_name(self,
                                  method: str,
                                  base_type: Type,
                                  args: List[Expression],
                                  arg_kinds: List[ArgKind],
                                  context: Context,
                                  original_type: Optional[Type] = None,
                                  object_node = None, method_node = None, return_node = None
                                  ) -> Tuple[Type, Type]:
        solved_methods = [
            '__setitem__',
            '__getitem__',
            '__enter__',
            '__iter__',
            '__next__',
            '__exit__'
        ]
        local_errors = self.msg
        original_type = original_type or base_type
        base_type = get_proper_type(base_type)
        if isinstance(context, OpExpr) or isinstance(context, ComparisonExpr) or isinstance(context, UnaryExpr) or method in solved_methods:
            base_types = base_type
            callee_types = []
            ret_types = []
            has_method = False
            ok = False
            for base_type in base_types: 
                callee_type = analyze_member_access(method, base_type, context, False, False, True,
                                                        local_errors, original_type=base_type,
                                                        chk=self.chk,
                                                        in_literal_context=self.is_literal_context(), object_node = object_node, member_expr=method_node)
                callee_types.append(callee_type)
                if not isinstance(callee_type, AnyType): 
                    has_method = True
            start = time.time()
            for base_type in base_types: 
                if method == '__getitem__' and isinstance(context, IndexExpr) and isinstance(base_type, TupleType) and self.try_getting_int_literals(context.index) is not None:
                    ns = self.try_getting_int_literals(context.index)
                    out = []
                    for n in ns:
                        if n < 0:
                            n += len(base_type.items)
                        if 0 <= n < len(base_type.items):
                            out.append(base_type.items[n])
                        else:
                            out.append(AnyType(0))
                    out = make_simplified_union(out)
                    e = context
                    self.add_infer_type((e, out), [(e.base, base_type), (e.index, next(iter(self.chk.type_map[e.index])))])
                    ret_type = out
                    ok = True
                else:
                    callee_type = analyze_member_access(method, base_type, context, False, False, True,
                                                            local_errors, original_type=base_type,
                                                            chk=self.chk,
                                                            in_literal_context=self.is_literal_context(), object_node = object_node)
                    if method =='__eq__' and isinstance(callee_type, CallableType) and isinstance(callee_type.arg_types[0], Instance) and callee_type.arg_types[0].type.fullname =='builtins.object':
                        if str(callee_type.arg_types[0]) == 'builtins.object' and isinstance(base_type, TypeVarType):
                            pass
                        else:
                            callee_type.arg_types[0] = base_type
                    callee_types.append(callee_type)
                    if isinstance(callee_type, AnyType): 
                        continue
                    else:
                        self.add_infer_type((method_node, callee_type), [(object_node, base_type)])
                        self.chk.dp_dag.pop(tuple([(method_node, callee_type)]), None)
                    corrects = []
                    ret_type, _ = self.check_method_call(method, base_type, callee_type, args, arg_kinds, context, local_errors, corrects = corrects, method_node = method_node)
                    if len(corrects) > 0 :
                        c0 = next(iter(corrects))
                        if len(corrects) > 0 and len(c0) > 0 and (len(c0) == 1 or isinstance(c0[1], Tuple)):
                            if len(ret_type) > 1: 
                                ret = make_simplified_union(ret_type)
                            else:
                                assert len(ret_type) == 1
                                ret = next(iter(ret_type))
                            c000 = next(iter(c0[0]))
                            if isinstance(c000, int): 
                                ok = True
                                self.add_infer_type((return_node, ret), [(method_node, callee_type)])
                            else:
                                ok_args = list(itertools.product(*corrects))
                                for args_now in ok_args:
                                    args_now = tuple([(x[0], x[1]) for x in args_now])
                                    ok = True
                                    self.add_infer_type((return_node, ret), [(method_node, callee_type)] + list(args_now))
                        elif len(corrects) > 0 and len(c0) > 0: 
                            for correct in corrects:
                                args_now, ret = correct
                                ok = True
                                if isinstance(args_now, int):
                                    self.add_infer_type((return_node, ret), [(method_node, callee_type)])
                                    break    
                                self.add_infer_type((return_node, ret), [(method_node, callee_type)] + list(args_now))
                    ret_types.extend(ret_type)
            if (len(ret_types) == 0 or not ok) and has_method:
                return [AnyType(0)], [AnyType(0)]
            if return_node is not None:
                return_node.type = ret_types
            self.chk.store_type(method_node, callee_types)
            self.chk.store_type(return_node, ret_types)
            return ret_types, callee_types
        else:
            method_type = analyze_member_access(method, base_type, context, False, False, True,
                                            local_errors, original_type=original_type,
                                            chk=self.chk,
                                            in_literal_context=self.is_literal_context())
            return self.check_method_call(
            method, base_type, method_type, args, arg_kinds, context, local_errors, method_node=method_node)
    def check_method_call(self,
                          method_name: str,
                          base_type: Type,
                          method_type: Type,
                          args: List[Expression],
                          arg_kinds: List[ArgKind],
                          context: Context,
                          local_errors: Optional[MessageBuilder] = None, corrects = None, method_node = None) -> Tuple[Type, Type]:
        callable_name = self.method_fullname(base_type, method_name)
        object_type = base_type if callable_name is not None else None
        return self.check_call(method_type, args, arg_kinds,
                               context, arg_messages=local_errors,
                               callable_name=callable_name, object_type=base_type, corrects = corrects, method_node=method_node)
    def check_op(self, method: str, base_type: Type,
                 arg: Expression, context: Context,
                 allow_reverse: bool = False, object_node = None, method_node = None, return_node = None) -> Tuple[Type, Type]:
        return self.check_method_call_by_name(
            method=method,
            base_type=base_type,
            args=[arg],
            arg_kinds=[ARG_POS],
            context=context,
            object_node = object_node, method_node = method_node, return_node = return_node
        )
    def check_boolean_op(self, e: OpExpr, context: Context) -> Set[Type]:
        """boolean operation ('and' or 'or')."""
        ctx = self.type_context[-1]
        left_type = self.accept(e.left, ctx)
        assert e.op in ('and', 'or')  
        if e.right_always:
            left_map, right_map = None, {}  
        elif e.right_unreachable:
            left_map, right_map = {}, None
        elif e.op == 'and':
            right_map, left_map = self.chk.find_isinstance_check(e.left)
        elif e.op == 'or':
            left_map, right_map = self.chk.find_isinstance_check(e.left)
        right_type = self.analyze_cond_branch(right_map, e.right, left_type)
        if right_map is None:
            if left_map is None:
                return {AnyType(0)}
            return left_type
        if left_map is None:
            if right_map is None:
                return {AnyType(0)}
            return right_type
        left_types = left_type
        restricted_left_types = []
        temp_left = TempNode(AnyType(0), desc='bool_op_node_left')
        for left_type in left_types:
            if e.op == 'and':
                restricted_left_type = false_only(left_type)
            elif e.op == 'or':
                restricted_left_type = true_only(left_type)
            self.add_infer_type((temp_left, restricted_left_type), [(e.left, left_type)])
            restricted_left_types.append(restricted_left_type)
        lefts = restricted_left_types
        rights = right_type
        ret_types = []
        for left_ in lefts:
            for right_ in rights:
                if is_same_type(left_, right_):
                    if_else_item = make_simplified_union([left_,  right_])
                    self.add_infer_type((e, if_else_item), [(temp_left, left_), (e.right, right_)])
                    ret_types.append(if_else_item)
                else:
                    self.add_incompatible(temp_left, left_, e.right, right_)
        if len(ret_types) == 0:
            ret_types.append(self.chk.named_type('builtins.bool'))
        return ret_types
    def check_list_multiply(self, e: OpExpr) -> Set[Type]:
        """Type check an expression of form '[...] * e'.
        Type inference is special-cased for this common construct.
        """
        left_type = self.accept(e.left)
        method_node = self.get_temp_nodes(AnyType(0), e)
        result, method_type = self.check_op('__mul__', left_type, e.right, e, object_node = e.left, method_node=method_node, return_node = e)
        e.method_type = method_type
        return result
    def visit_assignment_expr(self, e: AssignmentExpr) -> Set[Type]:
        value = self.accept(e.value)
        self.chk.check_assignment(e.target, e.value)
        self.chk.store_type(e.target, value)
        return value
    def visit_unary_expr(self, e: UnaryExpr) -> Set[Type]:
        """Type check an unary operation ('not', '-', '+' or '~')."""
        operand_type = self.accept(e.expr)
        op = e.op
        if op == 'not':
            result: Type = {self.bool_type()}
        else:
            method = operators.unary_op_methods[op]
            method_node = self.get_temp_nodes(method, e)
            result, method_type = self.check_method_call_by_name(method, operand_type, [], [], e, object_node=e.expr, method_node=method_node, return_node=e)
            e.method_type = method_type
        return result
    def visit_index_expr(self, e: IndexExpr) -> Set[Type]:
        """Type check an index expression (base[index]).
        """
        result = self.visit_index_expr_helper(e)
        result = self.narrow_type_from_binder(e, result)
        return result
    def visit_index_expr_helper(self, e: IndexExpr) -> Set[Type]:
        if e.analyzed:
            return self.accept(e.analyzed)
        left_type = self.accept(e.base)
        return self.visit_index_with_type(left_type, e)
    def visit_index_with_type(self, left_type: Type, e: IndexExpr,
                              original_type: Optional[ProperType] = None) -> Set[Type]:
        index = e.index
        self.accept(index)
        if isinstance(left_type, UnionType):
            original_type = original_type or left_type
            return make_simplified_union([self.visit_index_with_type(typ, e,
                                                                     original_type)
                                          for typ in left_type.relevant_items()],
                                         contract_literals=False)
        elif isinstance(left_type, TupleType): 
            if isinstance(index, SliceExpr):
                return self.visit_tuple_slice_helper(left_type, index)
            ns = self.try_getting_int_literals(index)
            if ns is not None:
                out = []
                for n in ns:
                    if n < 0:
                        n += len(left_type.items)
                    if 0 <= n < len(left_type.items):
                        out.append(left_type.items[n])
                    else:
                        out.append(AnyType(0))
                out = make_simplified_union(out)
                self.add_infer_type((e, out), [(e.base, left_type), (e.index, self.chk.type_map[e.index])])
                return out
            else:
                return self.nonliteral_tuple_index_helper(left_type, index, expr=e)
        elif isinstance(left_type, TypedDictType):
            return {AnyType(0)}
        elif (isinstance(left_type, CallableType)
              and left_type.is_type_obj() and left_type.type_object().is_enum):
            return {AnyType(0)}
        else:
            method_node = self.get_temp_nodes(AnyType(0), e)
            result, method_type = self.check_method_call_by_name(
                '__getitem__', left_type, [e.index], [ARG_POS], e,
                original_type=original_type, object_node = e.base, method_node = method_node, return_node = e)
            e.method_type = method_type
            return result
    def visit_tuple_slice_helper(self, left_type: TupleType, slic: SliceExpr) -> Set[Type]:
        begin: Sequence[Optional[int]] = [None]
        end: Sequence[Optional[int]] = [None]
        stride: Sequence[Optional[int]] = [None]
        if slic.begin_index:
            begin_raw = self.try_getting_int_literals(slic.begin_index)
            if begin_raw is None:
                return self.nonliteral_tuple_index_helper(left_type, slic)
            begin = begin_raw
        if slic.end_index:
            end_raw = self.try_getting_int_literals(slic.end_index)
            if end_raw is None:
                return self.nonliteral_tuple_index_helper(left_type, slic)
            end = end_raw
        if slic.stride:
            stride_raw = self.try_getting_int_literals(slic.stride)
            if stride_raw is None:
                return self.nonliteral_tuple_index_helper(left_type, slic)
            stride = stride_raw
        items: List[Type] = []
        for b, e, s in itertools.product(begin, end, stride):
            items.append(left_type.slice(b, e, s))
        return make_simplified_union(items)
    def try_getting_int_literals(self, index: Expression) -> Optional[List[int]]:
        if isinstance(index, IntExpr):
            return [index.value]
        elif isinstance(index, UnaryExpr):
            if index.op == '-':
                operand = index.expr
                if isinstance(operand, IntExpr):
                    return [-1 * operand.value]
        return None
    def nonliteral_tuple_index_helper(self, left_type: TupleType, index: Expression, expr:IndexExpr) -> Set[Type]:
        index_types = self.accept(index)
        ret = []
        for t in index_types:
            expected_type = UnionType.make_union([self.named_type('builtins.int'),
                                                self.named_type('builtins.slice')])
            if not self.chk.check_subtype(t, expected_type, index,
                                        message_registry.INVALID_TUPLE_INDEX_TYPE,
                                        'actual type', 'expected type'):
                self.add_single_incompatible(index, t)
                self.add_improvement_from_pair(index, t)
            else:
                union = make_simplified_union(left_type.items)
                if isinstance(index, SliceExpr):
                    tout =  self.chk.named_generic_type('builtins.tuple', [union])
                else:
                    tout =  union
                self.add_infer_type((expr, tout), [(expr.index, t), (expr.base, left_type)])
                ret.append(tout)
        if len(ret) > 0:
            return ret
        else:
            return [AnyType(0)]
    def visit_cast_expr(self, expr: CastExpr) -> Set[Type]:
        source_type = self.accept(expr.expr, type_context=AnyType(TypeOfAny.special_form))
        target_type = expr.type
        return target_type
    def visit_reveal_expr(self, expr: RevealExpr) -> Set[Type]:
        if expr.kind == REVEAL_TYPE:
            assert expr.expr is not None
            revealed_type = self.accept(expr.expr, type_context=self.type_context[-1])
            return revealed_type
        else:
            return {NoneType()}
    def visit_type_application(self, tapp: TypeApplication) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_type_alias_expr(self, alias: TypeAliasExpr) -> Set[Type]:
        return {AnyType(0)}
    def visit_list_expr(self, e: ListExpr) -> Set[Type]:
        return self.check_lst_expr(e.items, 'builtins.list', '<list>', e)
    def visit_set_expr(self, e: SetExpr) -> Set[Type]:
        return self.check_lst_expr(e.items, 'builtins.set', '<set>', e)
    def check_lst_expr(self, items: List[Expression], fullname: str,
                       tag: str, context: Context) -> Set[Type]:
        tv = TypeVarType('T', 'T', -1, [], self.object_type())
        constructor = CallableType(
            [tv],
            [nodes.ARG_STAR],
            [None],
            self.chk.named_generic_type(fullname, [tv]),
            self.named_type('builtins.function'),
            name=tag,
            variables=[tv])
        temp_method = self.get_temp_nodes(constructor, context = context)
        self.chk.store_type(temp_method, constructor)
        corrects = []
        out = self.check_call(constructor,
                              [(i.expr if isinstance(i, StarExpr) else i)
                               for i in items],
                              [(nodes.ARG_STAR if isinstance(i, StarExpr) else nodes.ARG_POS)
                               for i in items],
                              context, 
                               corrects=corrects,method_node=temp_method)[0]
        for correct in corrects:
            args, ret = correct
            if isinstance(args, int):
                self.add_infer_type((context, ret), [(temp_method, constructor)])
                break    
            self.add_infer_type((context, ret), [(temp_method, constructor)] + list(args))
        return out 
    def visit_tuple_expr(self, e: TupleExpr) -> Set[Type]:
        items: List[Type] = []
        j = 0  
        for i in range(len(e.items)):
            item = e.items[i]
            if isinstance(item, StarExpr):
                tt = self.accept(item.expr)
                tt = get_proper_type(tt)
                if isinstance(tt, TupleType):
                    for tt_ in tt.items:
                        items.append([tt_])
                    j += len(tt.items)
                else:
                    return self.check_lst_expr(e.items, 'builtins.tuple', '<tuple>', e)
            else:
                tts = self.accept(item)
                items.append(tts)
        possible_items = itertools.product(*items)
        final_items = []
        for possible in possible_items: 
            fallback_item = AnyType(TypeOfAny.special_form)
            type_item =  TupleType(possible, self.chk.named_generic_type('builtins.tuple', [fallback_item]))
            self.add_infer_type((e, type_item), list(zip(e.items, possible)))
            final_items.append(type_item)
        return final_items
    def visit_dict_expr(self, e: DictExpr) -> Set[Type]:
        args: List[Expression] = []  
        for key, value in e.items:
                tup = TupleExpr([key, value])
                if key.line >= 0:
                    tup.line = key.line
                    tup.column = key.column
                else:
                    tup.line = value.line
                    tup.column = value.column
                args.append(tup)
        kt = TypeVarType('KT', 'KT', -1, [], self.object_type())
        vt = TypeVarType('VT', 'VT', -2, [], self.object_type())
        rv = None
        constructor = CallableType(
            [TupleType([kt, vt], self.named_type('builtins.tuple'))],
            [nodes.ARG_STAR],
            [None],
            self.chk.named_generic_type('builtins.dict', [kt, vt]),
            self.named_type('builtins.function'),
            name='<dict>',
            variables=[kt, vt])
        method_node = self.get_temp_nodes(constructor, context=e)
        self.chk.store_type(method_node, constructor)
        corrects = []
        ret = self.check_call(constructor, args, [nodes.ARG_POS] * len(args), e, corrects = corrects, method_node=method_node)
        rv = ret[0]
        if len(corrects) > 0:
            c0 = next(iter(corrects))
            if len(corrects) > 0 and len(c0) > 0 and (len(c0) == 1 or isinstance(c0[1], Tuple)):
                c000 = next(iter(c0[0]))
                if isinstance(c000, int):
                    self.add_infer_type((e, rv), [(method_node, constructor)])
                else:
                    ok_args = list(itertools.product(*corrects))
                    for args in ok_args:
                        args = tuple([(x[0], x[1]) for x in args])
                        self.add_infer_type((e, rv), [(method_node, constructor)] + list(args))
            elif len(corrects) > 0 and len(c0) > 0:
                for c in corrects:
                    args = c[0]
                    ret = c[1]
                    if isinstance(args, int):
                        self.add_infer_type((e, ret), [(method_node, constructor)])
                        break    
                    else:
                        self.add_infer_type((e, ret), [(method_node, constructor)] + list(args))
        assert rv is not None
        return rv
    def visit_lambda_expr(self, e: LambdaExpr) -> Set[Type]:
        self.chk.check_default_args(e, body_is_trivial=False)
        self.chk.return_types.append(AnyType(TypeOfAny.special_form))
        with self.chk.scope.push_function(e):
            for stmt in e.body.body[:-1]:
                stmt.accept(self.chk)
            ret_type = self.accept(e.expr())
        fallback = self.named_type('builtins.function')
        self.chk.return_types.pop()
        return {callable_type(e, fallback, ret_type)}
    def visit_super_expr(self, e: SuperExpr) -> Set[Type]:
        return {AnyType(0)}
    def visit_slice_expr(self, e: SliceExpr) -> Set[Type]:
        expected = make_optional_type(self.named_type('builtins.int'))
        precondition = []
        for index in [e.begin_index, e.end_index, e.stride]:
            index_condition = []
            if index:
                ts = self.accept(index)
                for t in ts:
                    if not is_subtype(t, expected):
                        self.add_single_incompatible(index, t)
                        self.add_improvement_from_pair(index, t)
                    else:
                        index_condition.append((index, t))
                precondition.append(index_condition)
        possible_condition = itertools.product(*precondition)
        slice_type = self.named_type('builtins.slice')
        for possible in possible_condition:
            self.add_infer_type((e, slice_type), list(possible))
        return slice_type
    def visit_list_comprehension(self, e: ListComprehension) -> Set[Type]:
        ret_types = self.check_generator_or_comprehension(
            e.generator, 'builtins.list', '<list-comprehension>')
        for r in ret_types:
            self.add_infer_type((e, r),[(e.generator, r)])
        return ret_types
    def visit_set_comprehension(self, e: SetComprehension) -> Set[Type]:
        ret_types = self.check_generator_or_comprehension(
            e.generator, 'builtins.set', '<set-comprehension>')
        for r in ret_types:
            self.add_infer_type((e, r),[(e.generator, r)])
        return ret_types
    def visit_generator_expr(self, e: GeneratorExpr) -> Set[Type]:
        typ = 'typing.Generator'
        additional_args = [NoneType(), NoneType()]
        return self.check_generator_or_comprehension(e, typ, '<generator>',
                                                     additional_args=additional_args)
    def check_generator_or_comprehension(self, gen: GeneratorExpr,
                                         type_name: str,
                                         id_for_messages: str,
                                         additional_args: Optional[List[Type]] = None) -> Set[Type]:
        additional_args = additional_args or []
        with self.chk.binder.frame_context(can_skip=True, fall_through=0):
            self.check_for_comp(gen)
            tv = TypeVarType('T', 'T', -1, [], self.object_type())
            tv_list: List[Type] = [tv]
            constructor = CallableType(
                tv_list,
                [nodes.ARG_POS],
                [None],
                self.chk.named_generic_type(type_name, tv_list + additional_args),
                self.chk.named_type('builtins.function'),
                name=id_for_messages,
                variables=[tv])
            method_node = self.get_temp_nodes(constructor, context=gen)
            self.chk.store_type(method_node, constructor)
            corrects = []
            ret = self.check_call(constructor,
                                [gen.left_expr], [nodes.ARG_POS], gen, corrects = corrects, method_node=method_node)
            ret_type = ret[0]
            if len(corrects) > 0:
                c0 = next(iter(corrects))
                if len(corrects) > 0 and len(c0) > 0 and (len(c0) == 1 or isinstance(c0[1], Tuple)):
                    if isinstance(corrects[0][0][0], int):
                        self.add_infer_type((gen, ret_type), [(method_node, constructor)])
                    else:
                        ok_args = list(itertools.product(*corrects))
                        for args in ok_args:
                            args = tuple([(x[0], x[1]) for x in args])
                            self.add_infer_type((gen, ret_type), [(method_node, constructor)] + list(args))
                elif len(corrects) > 0 and len(c0) > 0:
                    for c in corrects:
                        args = c[0]
                        ret = c[1]
                        if isinstance(args, int):
                            self.add_infer_type((gen, ret), [(method_node, constructor)])
                            break    
                        else:
                            self.add_infer_type((gen, ret), [(method_node, constructor)] + list(args))
            return ret_type
    def visit_dictionary_comprehension(self, e: DictionaryComprehension) -> Set[Type]:
        with self.chk.binder.frame_context(can_skip=True, fall_through=0):
            self.check_for_comp(e)
            ktdef = TypeVarType('KT', 'KT', -1, [], self.object_type())
            vtdef = TypeVarType('VT', 'VT', -2, [], self.object_type())
            constructor = CallableType(
                [ktdef, vtdef],
                [nodes.ARG_POS, nodes.ARG_POS],
                [None, None],
                self.chk.named_generic_type('builtins.dict', [ktdef, vtdef]),
                self.chk.named_type('builtins.function'),
                name='<dictionary-comprehension>',
                variables=[ktdef, vtdef])
            return self.check_call(constructor,
                                   [e.key, e.value], [nodes.ARG_POS, nodes.ARG_POS], e)[0]
    def check_for_comp(self, e: Union[GeneratorExpr, DictionaryComprehension]) -> None:
        for index, sequence, conditions in zip(e.indices, e.sequences,
                                                         e.condlists):
            _, sequence_type, ret_node = self.chk.analyze_iterable_item_type(sequence)
            self.chk.analyze_index_variables(index, sequence_type, True, e, ret_node)
            for condition in conditions:
                self.accept(condition)
                true_map, false_map = self.chk.find_isinstance_check(condition)
                if true_map:
                    self.chk.push_type_map(true_map)
    def visit_conditional_expr(self, e: ConditionalExpr) -> Set[Type]:
        self.accept(e.cond)
        ctx = self.type_context[-1]
        if_map, else_map = self.chk.find_isinstance_check(e.cond)
        if_type = self.analyze_cond_branch(if_map, e.if_expr, context=ctx)
        else_type = self.analyze_cond_branch(else_map, e.else_expr, context=ctx)
        if_items = if_type
        else_items = else_type
        ret_types = []
        if isinstance(else_type, UninhabitedType):
            for if_item in if_items:
                self.add_infer_type((e, if_item), [(e.if_expr, if_item)])
                ret_types.append(if_item)
        elif isinstance(if_type, UninhabitedType):
            for else_item in else_items:
                self.add_infer_type((e, else_item), [(e.else_expr, else_item)])
                ret_types.append(else_item)
        else:
            for if_item in if_items:
                for else_item in else_items:
                    if is_same_type(if_item, else_item):
                        if_else_item = make_simplified_union([if_item, else_item])
                        self.add_infer_type((e, if_else_item), [(e.if_expr, if_item), (e.else_expr, else_item)])
                        ret_types.append(if_else_item)
                    else:
                        self.add_incompatible(e.if_expr, if_item, e.else_expr, else_item)
        return ret_types
    def analyze_cond_branch(self, map: Optional[Dict[Expression, Type]],
                            node: Expression, context: Optional[Type]) -> Set[Type]:
        with self.chk.binder.frame_context(can_skip=True, fall_through=0):
            if map is None:
                self.accept(node, type_context=context)
                return UninhabitedType()
            self.chk.push_type_map(map)
            return self.accept(node, type_context=context)
    def visit_backquote_expr(self, e: BackquoteExpr) -> Set[Type]:
        self.accept(e.expr)
        return {self.named_type('builtins.str')}
    def accept(self,
               node: Expression,
               type_context: Optional[Type] = None, cache=True) -> Set[Type]:
        self.chk.manager.lexical_stat[type(node)].add(node)
        if isinstance(type_context, (set, list)):
            if len(type_context) == 0:
                type_context = None
            else:
                type_context = next(iter(type_context))
        self.type_context.append(type_context)
        if cache and (node, type_context) in self.chk.cache_type_map:
            return self.chk.cache_type_map[(node, type_context)]
        if isinstance(node, CallExpr):
            typ = self.visit_call_expr(node)
        elif isinstance(node, YieldFromExpr):
            typ = self.visit_yield_from_expr(node)
        elif isinstance(node, ConditionalExpr):
            typ = self.visit_conditional_expr(node)
        else:
            typ = node.accept(self)
        self.type_context.pop()
        assert typ is not None
        if isinstance(typ, Type):
            typ = {typ}
        self.chk.store_type(node, typ)
        self.chk.cache_type_map[(node, type_context)] = typ
        if self.chk.current_node_deferred:
            return {AnyType(0)}
        else:
            return set(typ)
    def named_type(self, name: str) -> Instance:
        """Return an instance type with type given by the name and no type
        arguments. Alias for TypeChecker.named_type.
        """
        return self.chk.named_type(name)
    def not_ready_callback(self, name: str, context: Context) -> None:
        self.chk.handle_cannot_determine_type(name, context)
    def visit_yield_expr(self, e: YieldExpr) -> Set[Type]:
        return {AnyType(0)}
    def visit_await_expr(self, e: AwaitExpr) -> Set[Type]:
        return {AnyType(0)}
    def visit_yield_from_expr(self, e: YieldFromExpr) -> Set[Type]:
        return {AnyType(0)}
    def visit_temp_node(self, e: TempNode) -> Set[Type]:
        if isinstance(e.context, NameExpr):
            return self.visit_name_expr(e)
        else:
            return e.type
    def visit_type_var_expr(self, e: TypeVarExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_paramspec_expr(self, e: ParamSpecExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_newtype_expr(self, e: NewTypeExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_namedtuple_expr(self, e: NamedTupleExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_enum_call_expr(self, e: EnumCallExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit_typeddict_expr(self, e: TypedDictExpr) -> Set[Type]:
        return {AnyType(TypeOfAny.special_form)}
    def visit__promote_expr(self, e: PromoteExpr) -> Set[Type]:
        return {e.type}
    def visit_star_expr(self, e: StarExpr) -> StarType:
        return {AnyType(TypeOfAny.special_form)}
    def object_type(self) -> Instance:
        """Return instance type 'object'."""
        return self.named_type('builtins.object')
    def bool_type(self) -> Instance:
        """Return instance type 'bool'."""
        return self.named_type('builtins.bool')
    @overload
    def narrow_type_from_binder(self, expr: Expression, known_type: Type) -> Set[Type]: ...
    @overload
    def narrow_type_from_binder(self, expr: Expression, known_type: Type,
                                skip_non_overlapping: bool) -> Optional[Type]: ...
    def narrow_type_from_binder(self, expr: Expression, known_types: Type,
                                skip_non_overlapping: bool = False) -> Optional[Type]:
        if literal(expr) >= LITERAL_TYPE:
            restriction = self.chk.binder.get(expr)
            if restriction is None:
                return known_types
            if isinstance(restriction, (set, list)):
                return restriction
            if isinstance(restriction, UninhabitedType):
                return restriction
        return known_types
def is_non_empty_tuple(t: Type) -> bool:
    t = get_proper_type(t)
    return isinstance(t, TupleType) and bool(t.items)
def is_duplicate_mapping(mapping: List[int],
                         actual_types: List[Type],
                         actual_kinds: List[ArgKind]) -> bool:
    return (
        len(mapping) > 1
        and not (len(mapping) == 2
                 and actual_kinds[mapping[0]] == nodes.ARG_STAR
                 and actual_kinds[mapping[1]] == nodes.ARG_STAR2)
        and not all(actual_kinds[m] == nodes.ARG_STAR2 and
                    not isinstance(get_proper_type(actual_types[m]), TypedDictType)
                    for m in mapping)
    )
