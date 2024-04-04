"""Mechanisms for inferring function types based on callsites.

Currently works by collecting all argument types at callsites,
synthesizing a list of possible function types from that, trying them
all, and picking the one with the fewest errors that we think is the
"best".

Can return JSON that pyannotate can use to apply the annotations to code.

There are a bunch of TODOs here:
 * Maybe want a way to surface the choices not selected??
 * We can generate an exponential number of type suggestions, and probably want
   a way to not always need to check them all.
 * Our heuristics for what types to try are primitive and not yet
   supported by real practice.
 * More!

Other things:
 * This is super brute force. Could we integrate with the typechecker
   more to understand more about what is going on?
 * Like something with tracking constraints/unification variables?
 * No understanding of type variables at *all*
"""

from typing import (
    List, Optional, Tuple, Dict, Callable, Union, NamedTuple, TypeVar, Iterator, cast,
)
from typing_extensions import TypedDict

from extyper.state import strict_optional_set
from extyper.types import (
    Type, AnyType, TypeOfAny, CallableType, Overloaded, UnionType, NoneType, Instance, TupleType,
    TypeVarType, FunctionLike, UninhabitedType,
    TypeStrVisitor, TypeTranslator,
    is_optional, remove_optional, ProperType, get_proper_type,
    TypedDictType, TypeAliasType, UninhabitedType
)
from extyper import nodes
from extyper.build import State, Graph
from extyper.nodes import (
    ArgKind, ARG_STAR, ARG_STAR2, FuncDef, MypyFile, SymbolTable,
    Decorator, RefExpr, Var, FakeInfo, 
    SymbolNode, TypeInfo, Expression, ReturnStmt, CallExpr, OpExpr, ComparisonExpr, 
    reverse_builtin_aliases,NameExpr, MemberExpr, ForStmt, AssignmentStmt, TupleExpr, GeneratorExpr, IfStmt, ConditionalExpr
)
from extyper.server.update import FineGrainedBuildManager
from extyper.util import split_target
from extyper.find_sources import SourceFinder, InvalidSourceList
from extyper.modulefinder import PYTHON_EXTENSIONS
from extyper.plugin import Plugin, FunctionContext, MethodContext
from extyper.traverser import TraverserVisitor
from extyper.checkexpr import has_any_type, map_actuals_to_formals
from extyper.subtypes import (
    is_subtype, is_equivalent, is_proper_subtype, is_more_precise,
    restrict_subtype_away, is_subtype_ignoring_tvars, is_callable_compatible,
    unify_generic_callable, find_member
)
from extyper.join import join_type_list
from extyper.meet import meet_type_list, meet_types
from extyper.sametypes import is_same_type
from extyper.typeops import make_simplified_union
from difflib import SequenceMatcher
from contextlib import contextmanager

import itertools
import json
import os
from copy import deepcopy
import time
PyAnnotateSignature = TypedDict('PyAnnotateSignature',
                                {'return_type': str, 'arg_types': List[str]})


Callsite = NamedTuple(
    'Callsite',
    [('path', str),
     ('line', int),
     ('arg_kinds', List[List[ArgKind]]),
     ('callee_arg_names', List[Optional[str]]),
     ('arg_names', List[List[Optional[str]]]),
     ('arg_types', List[List[Type]])])


class SuggestionPlugin(Plugin):
    """Plugin that records all calls to a given target."""

    def __init__(self, target: str) -> None:
        if target.endswith(('.__new__', '.__init__')):
            target = target.rsplit('.', 1)[0]

        self.target = target
        # List of call sites found by dmypy suggest:
        # (path, line, <arg kinds>, <arg names>, <arg types>)
        self.mystery_hits: List[Callsite] = []

    def get_function_hook(self, fullname: str
                          ) -> Optional[Callable[[FunctionContext], Type]]:
        if fullname == self.target:
            return self.log
        else:
            return None

    def get_method_hook(self, fullname: str
                        ) -> Optional[Callable[[MethodContext], Type]]:
        if fullname == self.target:
            return self.log
        else:
            return None

    def log(self, ctx: Union[FunctionContext, MethodContext]) -> Type:
        self.mystery_hits.append(Callsite(
            ctx.api.path,
            ctx.context.line,
            ctx.arg_kinds,
            ctx.callee_arg_names,
            ctx.arg_names,
            ctx.arg_types))
        return ctx.default_return_type


# NOTE: We could make this a bunch faster by implementing a StatementVisitor that skips
# traversing into expressions
class ReturnFinder(TraverserVisitor):
    """Visitor for finding all types returned from a function."""
    def __init__(self, typemap: Dict[Expression, Type]) -> None:
        self.typemap = typemap
        self.return_types = []

    def visit_return_stmt(self, o: ReturnStmt) -> None:
        if o.expr is not None and o.expr in self.typemap:
            self.return_types.append((o.expr, self.typemap[o.expr]))

    def visit_func_def(self, o: FuncDef) -> None:
        # Skip nested functions
        pass


def get_return_types(typemap: Dict[Expression, Type], func: FuncDef) -> List[Type]:
    """Find all the types returned by return statements in func."""
    finder = ReturnFinder(typemap)
    func.body.accept(finder)
    return finder.return_types

class DependencyFinder(TraverserVisitor):
    def __init__(self, nodes: List[FuncDef]) -> None:
        self.nodes = nodes
        self.depenency = set()
    def visit_call_expr(self, o: CallExpr) -> None:
        if hasattr(o.callee, 'node'):
            if o.callee.node in self.nodes:
                self.depenency.add(o.callee.node)
class VarDependencyFinder(TraverserVisitor):
    def __init__(self, nodes) -> None:
        self.arg_dependency = {node:[] for node in nodes}
        self.build_dependency = {node:[] for node in nodes}
    def visit_op_expr(self, o: OpExpr) -> None:
        pass
        # if isinstance(o.right, RefExpr) and o.right.node in self.arg_types:
        #     self.arg_types[o.right.node].append(get_proper_type(self.typemap.get(o.left)))
        # elif isinstance(o.left, RefExpr) and o.left.node in self.arg_types:
        #     self.arg_types[o.left.node].append(get_proper_type(self.typemap.get(o.right)))
    def visit_for_stmt(self, s: ForStmt) -> None:
        pass
    def visit_comparison_expr(self, o: ComparisonExpr) -> None:
        pass
        # for operand in o.operands:
        #     if isinstance(operand, RefExpr) and operand.node in self.arg_types:
        #         for operand2 in o.operands:
        #             if operand2 == operand:
        #                 continue
        #             self.arg_types[operand.node].append(get_proper_type(self.typemap.get(operand2)))
    def visit_member_expr(self, o: MemberExpr):
        if o in self.arg_dependency:
            if o.expr in self.arg_dependency:
                self.arg_dependency[o.expr].append(o)
        super().visit_member_expr(o)
        # if o.expr.node in self.arg_attrs:
        #     self.arg_attrs[o.expr.node].append(o.name)
    def visit_call_expr(self, o: CallExpr) -> None:
        if o.callee in self.arg_dependency:
            for arg in o.args:
                if arg in self.arg_dependency:
                    self.arg_dependency[o.callee].append(arg)
        if isinstance(o.callee, MemberExpr):
            self.visit_member_expr(o.callee)
        # if not any(isinstance(e, RefExpr) and e.node in self.arg_types for e in o.args):
        #     return

        # typ = get_proper_type(self.typemap.get(o.callee))
        # if o.callee.node in self.changed_func:
        #     typ = get_proper_type(self.changed_func.get(o.callee.node))
        # else:
        #     typ = get_proper_type(self.typemap.get(o.callee))
        # if not isinstance(typ, CallableType):
        #     if isinstance(typ, Overloaded):
        #         typ = get_proper_type(typ.items[0])
        #     if not isinstance(typ, CallableType):
        #         return

        # formal_to_actual = map_actuals_to_formals(
        #     o.arg_kinds, o.arg_names, typ.arg_kinds, typ.arg_names,
        #     lambda n: AnyType(TypeOfAny.special_form))

        # for i, args in enumerate(formal_to_actual):
        #     for arg_idx in args:
        #         arg = o.args[arg_idx]
        #         if isinstance(arg, RefExpr) and arg.node in self.arg_types:
        #             self.arg_types[arg.node].append(typ.arg_types[i])
    
    # def visit_call_expr(self, o: CallExpr) -> None:
    #     pass
        # if hasattr(o.callee, 'expr'):
        #     if hasattr(o.callee.expr, 'node') and o.callee.expr.node in self.arg_dependency:
        #         for arg in o.args:
        #             if isinstance(arg, NameExpr) and arg.node in self.arg_dependency:
        #                 self.arg_dependency[o.callee.expr.node].append(arg.node)
        #                 self.arg_dependency[arg.node].append(o.callee.expr.node)
        #                 self.build_dependency[arg.node].append(o.callee.expr.node)
        
class VarDependencyFinderOnlyArgs(TraverserVisitor):
    def __init__(self, func: FuncDef) -> None:
        self.arg_dependency: Dict[SymbolNode, List[SymbolNode]] = {arg.variable: [] for arg in func.arguments}
        self.build_dependency: Dict[SymbolNode, List[SymbolNode]] = {arg.variable: [] for arg in func.arguments}
    def visit_op_expr(self, o: OpExpr) -> None:
        pass
        # if isinstance(o.right, RefExpr) and o.right.node in self.arg_types:
        #     self.arg_types[o.right.node].append(get_proper_type(self.typemap.get(o.left)))
        # elif isinstance(o.left, RefExpr) and o.left.node in self.arg_types:
        #     self.arg_types[o.left.node].append(get_proper_type(self.typemap.get(o.right)))
    def visit_for_stmt(self, s: ForStmt) -> None:
        pass
    def visit_comparison_expr(self, o: ComparisonExpr) -> None:
        pass
        # for operand in o.operands:
        #     if isinstance(operand, RefExpr) and operand.node in self.arg_types:
        #         for operand2 in o.operands:
        #             if operand2 == operand:
        #                 continue
        #             self.arg_types[operand.node].append(get_proper_type(self.typemap.get(operand2)))
    def visit_member_expr(self, o: MemberExpr):
        pass
        # if o.expr.node in self.arg_attrs:
        #     self.arg_attrs[o.expr.node].append(o.name)
    def visit_call_expr(self, o: CallExpr) -> None:
        pass
        # if isinstance(o.callee,MemberExpr):
        #     self.visit_member_expr(o.callee)
        # if not any(isinstance(e, RefExpr) and e.node in self.arg_types for e in o.args):
        #     return

        # typ = get_proper_type(self.typemap.get(o.callee))
        # if o.callee.node in self.changed_func:
        #     typ = get_proper_type(self.changed_func.get(o.callee.node))
        # else:
        #     typ = get_proper_type(self.typemap.get(o.callee))
        # if not isinstance(typ, CallableType):
        #     if isinstance(typ, Overloaded):
        #         typ = get_proper_type(typ.items[0])
        #     if not isinstance(typ, CallableType):
        #         return

        # formal_to_actual = map_actuals_to_formals(
        #     o.arg_kinds, o.arg_names, typ.arg_kinds, typ.arg_names,
        #     lambda n: AnyType(TypeOfAny.special_form))

        # for i, args in enumerate(formal_to_actual):
        #     for arg_idx in args:
        #         arg = o.args[arg_idx]
        #         if isinstance(arg, RefExpr) and arg.node in self.arg_types:
        #             self.arg_types[arg.node].append(typ.arg_types[i])
    
    # def visit_call_expr(self, o: CallExpr) -> None:
    #     pass
        # if hasattr(o.callee, 'expr'):
        #     if hasattr(o.callee.expr, 'node') and o.callee.expr.node in self.arg_dependency:
        #         for arg in o.args:
        #             if isinstance(arg, NameExpr) and arg.node in self.arg_dependency:
        #                 self.arg_dependency[o.callee.expr.node].append(arg.node)
        #                 self.arg_dependency[arg.node].append(o.callee.expr.node)
        #                 self.build_dependency[arg.node].append(o.callee.expr.node)
class AssignFinder(TraverserVisitor):
    def __init__(self, func: FuncDef):
        self.assigns = {arg.variable: [] for arg in func.arguments}
    
    def visit_assignment_stmt(self, s: AssignmentStmt):
        if isinstance(s.rvalue, NameExpr) and s.rvalue.node in self.assigns:
            self.assigns[s.rvalue.node].extend(s.lvalues)

class DependencyGraph():
    def __init__(self, func: FuncDef, state):
        var_dependency_finder = VarDependencyFinderOnlyArgs(func)
        func.body.accept(var_dependency_finder)
        self.arg_dependency = var_dependency_finder.arg_dependency
        self.build_dependency = var_dependency_finder.build_dependency
        args = [x.variable for x in func.arguments]
        for arg in args:
            for u in state._type_checker.check_dependency_map:
                if isinstance(u, NameExpr) and isinstance(u.node, Var) and u.node == arg:
                    for v in state._type_checker.check_dependency_map[u]:
                        # check if v depends on other args
                        arg2 = self.determine(args, v, state._type_checker.infer_dependency_map)
                        if arg2 is not None:
                            self.build_dependency[arg].append(arg2)
                            self.arg_dependency[arg].append(arg2)
                            self.arg_dependency[arg2].append(arg)
        self.arg_dependency = var_dependency_finder.arg_dependency
        self.build_dependency = var_dependency_finder.build_dependency
        self.start_points = []
        self.visited = []
        # 无向图连通块
        self.blocks = []
        for u in self.arg_dependency:
            # if len(self.arg_dependency[u]) == 0:
                # self.start_points.append(u)
            if u in self.visited:
                continue
            block = []
            self.dfs(u, block)   
            self.blocks.append(block)
        self.typo_order = []
        build_dependency = self.build_dependency
        for block in self.blocks:
            deque = []
            for u in block:
                if len(build_dependency[u]) == 0:
                    build_dependency.pop(u)
                    deque.append(u)
            typo = []
            while len(deque) > 0:
                u = deque.pop()
                typo.append(u)
                dels = []
                for v in build_dependency:
                    if v not in block:
                        continue
                    if u in build_dependency[v]:
                        build_dependency[v].remove(u)
                    if len(build_dependency[v]) == 0:
                        deque.append(v)
                        dels.append(v)
                for v in dels:
                    build_dependency.pop(v)
                dels = []
            for v in build_dependency:
                if v not in block:
                    continue
                typo.append(v)
            self.typo_order.extend(typo)
    def determine(self, args, v, infer_dependency_map):
        if isinstance(v, NameExpr):
            if v.node in args:
                return v.node
    def dfs(self, u, block):
        block.append(u)
        self.visited.append(u)
        for v in self.arg_dependency[u]:
            if v in self.visited:
                continue
            self.dfs(v, block)

class ArgUseGlobalFinder(TraverserVisitor):
    """Visitor for finding all the types of arguments that each arg is passed to.

    This is extremely simple minded but might be effective anyways.
    """
    def __init__(self, func: FuncDef, typemap: Dict[Expression, Type], changed_func: Dict[FuncDef, Type], assigns) -> None:
        self.typemap = typemap
        self.func = func
        self.arg_types: Dict[SymbolNode, List[Type]] = {arg.variable: [] for arg in func.arguments}
        self.arg_attrs: Dict[SymbolNode, str] = {arg.variable: [] for arg in func.arguments}
        
        self.callable_recording: Dict[SymbolNode, CallExpr] = {arg.variable: [] for arg in func.arguments}
        self.arg_types_union: Dict[SymbolNode, List[List[Type]]] = {arg.variable: [] for arg in func.arguments}
        self.back_assigns = {}
        self.assigns = assigns
        for k in self.assigns:
            for assign in self.assigns[k]:
                if isinstance(assign, MemberExpr):
                    self.back_assigns[self.get_proper_name(assign.expr.fullname , assign.name)] = k
        self.changed_func = changed_func
    def get_proper_name(self, callee, caller):
        if callee is None:
            if caller is None:
                return ''
            else:
                return caller
        else:
            return callee + '.' + caller
    def visit_conditional_expr(self, e: ConditionalExpr) -> None:
        super().visit_conditional_expr(e)
    def visit_if_stmt(self, s: IfStmt) -> None:
        # for term in s.expr:
        #     if term.node in self.arg_types:
        #         self.arg_types[term.node].append(typ.arg_types[i])
        #     if isinstance(arg, MemberExpr):
        #         name = self.get_proper_name(arg.expr.fullname , arg.name)
        #         if name in self.back_assigns:
        #             self.arg_types[self.back_assigns[name]].append(typ.arg_types[i])
        super().visit_if_stmt(s)
    def visit_op_expr(self, o: OpExpr) -> None:
        # if isinstance(o.right, RefExpr) and o.right.node in self.arg_types:
        #     self.arg_types[o.right.node].append(get_proper_type(self.typemap.get(o.left)))
        # elif isinstance(o.left, RefExpr) and o.left.node in self.arg_types:
        #     self.arg_types[o.left.node].append(get_proper_type(self.typemap.get(o.right)))
        
        super().visit_op_expr(o)
    def visit_for_stmt(self, s: ForStmt) -> None:
        super().visit_for_stmt(s)
    def visit_generator_expr(self, e: GeneratorExpr) -> None:
        for sequence in e.sequences:
            if hasattr(sequence, 'node') and sequence.node in self.arg_attrs:
                self.arg_attrs[sequence.node].append('__iter__')
        super().visit_generator_expr(e)
    def visit_comparison_expr(self, o: ComparisonExpr) -> None:
        # for operand in o.operands:
        #     if isinstance(operand, RefExpr) and operand.node in self.arg_types:
        #         for operand2 in o.operands:
        #             if operand2 == operand:
        #                 continue
        #             self.arg_types[operand.node].append(get_proper_type(self.typemap.get(operand2)))
        
        super().visit_comparison_expr(o)
    def visit_member_expr(self, o: MemberExpr):
        if isinstance(o.expr, NameExpr):
            if o.expr.node in self.arg_attrs:
                self.arg_attrs[o.expr.node].append(o.name)
        if isinstance(o.expr, MemberExpr) and hasattr(o.expr.expr, "fullname"):
            name = self.get_proper_name(o.expr.expr.fullname , o.expr.name)
            if name in self.back_assigns:
                print(name, o.name)
                self.arg_attrs[self.back_assigns[name]].append(o.name)
        super().visit_member_expr(o)
    def visit_call_expr(self, o: CallExpr) -> None:
        
        if hasattr(o.callee, 'node') and o.callee.node in self.callable_recording:
            self.callable_recording[o.callee.node].append(o)
        if hasattr(o.callee, 'node') and o.callee.node in self.changed_func:
            typ = get_proper_type(self.changed_func.get(o.callee.node))
        else:
            typ = get_proper_type(self.typemap.get(o.callee))

        # todo, uniontype
        if not isinstance(typ, CallableType):
            if isinstance(typ, Overloaded):
                
                a_union = {arg.variable: [] for arg in self.func.arguments}
                for t in typ.items:
                    typ = get_proper_type(t)
                    if not isinstance(typ, CallableType):
                        continue
                    if typ.is_generic():
                        continue
                    formal_to_actual = map_actuals_to_formals(
                        o.arg_kinds, o.arg_names, typ.arg_kinds, typ.arg_names,
                        lambda n: AnyType(TypeOfAny.special_form))
                    for i, args in enumerate(formal_to_actual):
                        for arg_idx in args:
                            arg = o.args[arg_idx]
                            if isinstance(arg, RefExpr):
                                if arg.node in self.arg_types:
                                    a_union[arg.node].append(typ.arg_types[i])
                                if isinstance(arg, MemberExpr) and hasattr(arg.expr, "fullname"):
                                    name = self.get_proper_name(arg.expr.fullname , arg.name) 
                                    if name in self.back_assigns:
                                        a_union[self.back_assigns[name]].append(typ.arg_types[i])
                for k in a_union:
                    if len(a_union[k]) > 0:
                        self.arg_types_union[k].append(a_union[k])  
                super().visit_call_expr(o)
            else:
                super().visit_call_expr(o)
                return
        else:
            if not isinstance(typ, CallableType):
                super().visit_call_expr(o)
                return
            if typ.is_generic():
                super().visit_call_expr(o)
                return
            formal_to_actual = map_actuals_to_formals(
                o.arg_kinds, o.arg_names, typ.arg_kinds, typ.arg_names,
                lambda n: AnyType(TypeOfAny.special_form))

            for i, args in enumerate(formal_to_actual):
                for arg_idx in args:
                    arg = o.args[arg_idx]
                    if isinstance(arg, RefExpr):
                        if arg.node in self.arg_types:
                            self.arg_types[arg.node].append(typ.arg_types[i])
                        if isinstance(arg, MemberExpr) and hasattr(arg.expr, "fullname"):
                            name = self.get_proper_name(arg.expr.fullname , arg.name) 
                            if name in self.back_assigns:
                                self.arg_types[self.back_assigns[name]].append(typ.arg_types[i])
            super().visit_call_expr(o)

class LeadingFinder(TraverserVisitor):
    """Visitor for finding all the types of arguments that each arg is passed to.

    This is extremely simple minded but might be effective anyways.
    """
    def __init__(self) -> None:
        pass
    def visit_name_expr(self, e) -> None:
        pass


class ArgTypeFinder(TraverserVisitor):
    def __init__(self, type_map):
        self.collected = []
        self.type_map = type_map
    def visit_member_expr(self, o: MemberExpr) -> None:
        callee = o
        if callee in self.type_map:
            callee = self.type_map[callee]
            if isinstance(callee, CallableType):
                for arg in callee.arg_types:
                    if isinstance(arg, UnionType):
                        for item in arg.items:
                            self.collected.append(item)
                    if isinstance(arg, Instance):
                        self.collected.append(arg)
        return super().visit_member_expr(o)
    def visit_call_expr(self, o: CallExpr) -> None:
        callee = o.callee
        if callee in self.type_map:
            callee = self.type_map[callee]
            if isinstance(callee, CallableType):
                for arg in callee.arg_types:
                    if isinstance(arg, Instance):
                        self.collected.append(arg)
        return super().visit_call_expr(o)
class ArgUseFinder(TraverserVisitor):
    """Visitor for finding all the types of arguments that each arg is passed to.

    This is extremely simple minded but might be effective anyways.
    """
    def __init__(self, func: FuncDef, typemap: Dict[Expression, Type], changed_func: Dict[FuncDef, Type]) -> None:
        self.typemap = typemap
        self.arg_types: Dict[SymbolNode, List[Type]] = {arg.variable: [] for arg in func.arguments}
        self.arg_attrs: Dict[SymbolNode, str] = {arg.variable: [] for arg in func.arguments}
        # self.
        self.changed_func = changed_func
    def visit_op_expr(self, o: OpExpr) -> None:
        if isinstance(o.right, RefExpr) and o.right.node in self.arg_types:
            self.arg_types[o.right.node].append(get_proper_type(self.typemap.get(o.left)))
        elif isinstance(o.left, RefExpr) and o.left.node in self.arg_types:
            self.arg_types[o.left.node].append(get_proper_type(self.typemap.get(o.right)))
    def visit_for_stmt(self, s: ForStmt) -> None:
        pass
    def visit_comparison_expr(self, o: ComparisonExpr) -> None:
        for operand in o.operands:
            if isinstance(operand, RefExpr) and operand.node in self.arg_types:
                for operand2 in o.operands:
                    if operand2 == operand:
                        continue
                    self.arg_types[operand.node].append(get_proper_type(self.typemap.get(operand2)))
    def visit_member_expr(self, o: MemberExpr):
        if isinstance(o.expr, NameExpr) and o.expr.node in self.arg_attrs:
            self.arg_attrs[o.expr.node].append(o.name)
    def visit_call_expr(self, o: CallExpr) -> None:
        if isinstance(o.callee, MemberExpr):
            self.visit_member_expr(o.callee)
        if not any(isinstance(e, RefExpr) and e.node in self.arg_types for e in o.args):
            return

        typ = get_proper_type(self.typemap.get(o.callee))
        if o.callee.node in self.changed_func:
            typ = get_proper_type(self.changed_func.get(o.callee.node))
        else:
            typ = get_proper_type(self.typemap.get(o.callee))
        if not isinstance(typ, CallableType):
            if isinstance(typ, Overloaded):
                typ = get_proper_type(typ.items[0])
            if not isinstance(typ, CallableType):
                return

        formal_to_actual = map_actuals_to_formals(
            o.arg_kinds, o.arg_names, typ.arg_kinds, typ.arg_names,
            lambda n: AnyType(TypeOfAny.special_form))

        for i, args in enumerate(formal_to_actual):
            for arg_idx in args:
                arg = o.args[arg_idx]
                if isinstance(arg, RefExpr) and arg.node in self.arg_types:
                    self.arg_types[arg.node].append(typ.arg_types[i])

def get_var_uses_global(pyfile):
    pass
def get_arg_uses(typemap: Dict[Expression, Type], changed_func: Dict[FuncDef, Type], func: FuncDef) -> List[List[Type]]:
    """Find all the types of arguments that each arg is passed to.

    For example, given
      def foo(x: int) -> None: ...
      def bar(x: str) -> None: ...
      def test(x, y):
          foo(x)
          bar(y)

    this will return [[int], [str]].
    """
    finder = ArgUseFinder(func, typemap, changed_func)
    func.body.accept(finder)
    return [finder.arg_types[arg.variable] for arg in func.arguments], [finder.arg_attrs[arg.variable] for arg in func.arguments]
def get_arg_global_uses(typemap: Dict[Expression, Type], changed_func: Dict[FuncDef, Type], func, pyfile, assigns) -> List[List[Type]]:
    """Find all the types of arguments that each arg is passed to.

    For example, given
      def foo(x: int) -> None: ...
      def bar(x: str) -> None: ...
      def test(x, y):
          foo(x)
          bar(y)

    this will return [[int], [str]].
    """
    finder = ArgUseGlobalFinder(func, typemap, changed_func, assigns)
    if hasattr(func, "info"):
        if isinstance(func.info, FakeInfo):
            func.body.accept(finder)
        else:
            func.info.defn.accept(finder)
    return [finder.arg_types[arg.variable] for arg in func.arguments], [finder.arg_attrs[arg.variable] for arg in func.arguments], [finder.callable_recording[arg.variable] for arg in func.arguments], [finder.arg_types_union[arg.variable] for arg in func.arguments]


class SuggestionFailure(Exception):
    pass


def is_explicit_any(typ: AnyType) -> bool:
    # Originally I wanted to count as explicit anything derived from an explicit any, but that
    # seemed too strict in some testing.
    # return (typ.type_of_any == TypeOfAny.explicit
    #         or (typ.source_any is not None and typ.source_any.type_of_any == TypeOfAny.explicit))
    # Important question: what should we do with source_any stuff? Does that count?
    # And actually should explicit anys count at all?? Maybe not!
    return typ.type_of_any == TypeOfAny.explicit


def is_implicit_any(typ: Type) -> bool:
    typ = get_proper_type(typ)
    return isinstance(typ, AnyType) and not is_explicit_any(typ)

class SuggestionEngine:
    """Engine for finding call sites and suggesting signatures."""

    def __init__(self, fgmanager: FineGrainedBuildManager,
                changed_func, 
                 *,
                 json: bool = None,
                 no_errors: bool = False,
                 no_any: bool = False,
                 try_text: bool = False,
                 flex_any: Optional[float] = None,
                 use_fixme: Optional[str] = None,
                 max_guesses: Optional[int] = None
                 ) -> None:
        self.fgmanager = fgmanager
        self.manager = fgmanager.manager
        self.plugin = self.manager.plugin
        self.graph = fgmanager.graph
        self.finder = SourceFinder(self.manager.fscache, self.manager.options)
        self.changed_func = changed_func
        self.give_json = json
        self.no_errors = no_errors
        self.try_text = try_text
        self.flex_any = flex_any
        if no_any:
            self.flex_any = 1.0

        self.max_guesses = max_guesses or 128
        self.use_fixme = use_fixme
        self.tree = None
        self.memory = {}
        self.all_times = 0
    def ordered_functions(self, functions: List[str])->List[str]:
        nodes = []
        all_info = {}
        for func in functions:  
            mod, func_name, node = self.find_node(func)
            nodes.append(node)
            all_info[node] = (mod, func_name)
        dependencys = {}
        deque = []
        for node in nodes:
            finder = DependencyFinder(nodes)
            node.body.accept(finder)
            node_dependency = list(finder.depenency)
            if len(node_dependency) == 0:
                deque.append(node)
            else:
                dependencys[node] = node_dependency
        funcs = []
        while len(deque) > 0:
            node = deque.pop(0)
            funcs.append((node, all_info[node]))
            dels = []
            for q in dependencys:
                if node in dependencys[q]:
                    dependencys[q].remove(node)
                if len(dependencys[q]) == 0:
                    deque.append(q)
                    dels.append(q)
            for q in dels:
                dependencys.pop(q)
        for q in dependencys:
            # loop
            funcs.append((node, all_info[node]))
        return funcs
    def clear():
        self.tree = None
    def suggest(self, function: str, user_types) -> str:
        """Suggest an inferred type for function."""
        mod, func_name, node = self.find_node(function)
        if len(node.arguments) == 0:
            return None
        # with self.restore_after(mod):
        with self.with_export_types():
            suggestion = self.get_suggestion_On(mod, node, user_types, global_type_map)

        if self.give_json:
            return self.json_suggestion(mod, func_name, node, suggestion)
        else:
            return self.format_signature(suggestion)
    def suggest_with_function(self, mod, func_name, node, user_types, global_type_map, global_incompatible) -> str:
            """Suggest an inferred type for function."""
            mod, func_name, node = self.find_node(mod + '.' + func_name)
            if len(node.arguments) == 0:
                return None
            # with self.restore_after(mod):
            with self.with_export_types():
                suggestion = self.get_suggestion_On(mod, node, user_types, global_type_map, global_incompatible)

            if self.give_json:
                return self.json_suggestion(mod, func_name, node, suggestion)
            else:
                return self.format_signature(suggestion)
    def suggest_callsites(self, function: str) -> str:
        """Find a list of call sites of function."""
        mod, _, node = self.find_node(function)
        with self.restore_after(mod):
            callsites, _ = self.get_callsites(node)

        return '\n'.join(dedup(
            ["%s:%s: %s" % (path, line, self.format_args(arg_kinds, arg_names, arg_types))
             for path, line, arg_kinds, _, arg_names, arg_types in callsites]
        ))

    @contextmanager
    def restore_after(self, module: str) -> Iterator[None]:
        """Context manager that reloads a module after executing the body.

        This should undo any damage done to the module state while mucking around.
        """
        return 
        try:
            yield
        finally:
            self.reload(self.graph[module])

    @contextmanager
    def with_export_types(self) -> Iterator[None]:
        """Context manager that enables the export_types flag in the body.

        This causes type information to be exported into the manager's all_types variable.
        """
        old = self.manager.options.export_types
        self.manager.options.export_types = True
        try:
            yield
        finally:
            self.manager.options.export_types = old

    def get_trivial_type(self, fdef: FuncDef) -> CallableType:
        """Generate a trivial callable type from a func def, with all Anys"""
        # The Anys are marked as being from the suggestion engine
        # since they need some special treatment (specifically,
        # constraint generation ignores them.)
        return CallableType(
            [AnyType(TypeOfAny.suggestion_engine) for a in fdef.arg_kinds],
            fdef.arg_kinds,
            fdef.arg_names,
            AnyType(TypeOfAny.suggestion_engine),
            self.builtin_type('builtins.function'))

    def get_starting_type(self, fdef: FuncDef) -> CallableType:
        if isinstance(fdef.type, CallableType):
            return make_suggestion_anys(fdef.type)
        else:
            return self.get_trivial_type(fdef)
    def rank(self, candidates, name):
        
        def collect_all_type_names(typ):
            if typ.fullname != "builtins.object":
                typ_names.append(typ.fullname)
            for typn in typ.bases:
                if hasattr(typn, "type"):
                    typn = typn.type
                    collect_all_type_names(typn)
        candidate_rank = []
        for candidate in candidates:
            if hasattr(candidate, "type"):
                typ = candidate.type
                typ_names = []
                collect_all_type_names(typ)
                lcsl = 0 
                for typ_name in typ_names:
                    if name is not None and typ_name is not None:
                        s = SequenceMatcher(None, name.lower(), typ_name.lower())
                        block = s.find_longest_match()
                        lcs = name.lower()[block.a:(block.a + block.size)]
                        lcsl = max(lcsl, len(lcs))

                candidate_rank.append((candidate, lcsl))
            else:
                candidate_rank.append((candidate, 0))
        
        candidate_rank = sorted(candidate_rank, key = lambda x: x[1], reverse=True)
        candidate = [x[0] for x in candidate_rank]
        previous_hints = self.memory.get(name, [])
        for hint in previous_hints:
            if isinstance(hint, AnyType):
                continue
            if hint in candidate:
                candidate.remove(hint)
            candidate.insert(0, hint)
    
    def get_args(self, is_method: bool,
                 base: CallableType, defaults: List[Optional[Type]],
                 callsites: List[Callsite],
                 uses: List[List[Type]], learnt: List[List[Type]], current_pos=None, user_types=None, attrs=None, callable_recording=None, arg_types_union=None) -> List[List[Type]]:
        """Produce a list of type suggestions for each argument type."""
        def all_base(uses):
            for x in uses:
                if hasattr(x, "type"):
                    if not x.type.fullname == 'builtins.object':
                        return False
                else:
                    return False
            return True
        types: List[List[Type]] = []
        for i in range(len(base.arg_kinds)):
            # Make self args Any but this will get overridden somewhere in the checker
            if i == 0 and is_method or (current_pos is not None and i != current_pos):
                types.append([AnyType(TypeOfAny.suggestion_engine)])
                continue
            # if (len(uses[i]) == 0 or all_base(uses[i])) and len(attrs[i]) == 0 and len(arg_types_union[i]) == 0:
            #     types.append([AnyType(TypeOfAny.suggestion_engine)])
            #     continue
            
            attr_ = attrs[i]
                # Todo: make it fast

            all_arg_types = []
            for call in callsites:
                for typ in call.arg_types[i - is_method]:
                    # Collect all the types except for implicit anys
                    if not is_implicit_any(typ):
                        all_arg_types.append(typ)
            all_arg_types_union = arg_types_union[i]
            all_use_types = []
            for typ in uses[i]:
                # Collect all the types except for implicit anys
                if not is_implicit_any(typ):
                    all_use_types.append(typ)
            
            
            # Add in any default argument types
            # default = defaults[i]
            # if default:
            #     all_arg_types.append(default)
            #     if all_use_types:
            #         all_use_types.append(default)

            arg_types = []
            for typ in user_types:
                flag = 0
                for use_types in all_use_types:
                    if not is_subtype(typ, use_types):
                        print(typ)
                        print(use_types)
                        
                        flag = 1
                        break
                for arg_types_union in all_arg_types_union:
                    if not any([is_subtype(typ, use_types) for use_types in arg_types_union]):
                        flag = 1
                        break
                if flag == 1:
                    continue
                if isinstance(typ, UnionType):
                    type_first = typ.items[0]
                    if all([(attr in type_first.type.names or attr in type_first.type.protocol_members) for attr in attr_]):
                        arg_types.append(typ)
                else:
                    if all([(attr in typ.type.names or attr in typ.type.protocol_members) for attr in attr_]):
                        if not isinstance(typ, UninhabitedType):
                            arg_types.append(typ)
                    else:
                        print('fail attr')
                        print(typ)
            for use_types in all_use_types:
                arg_types.append(use_types)
            
            self.rank(arg_types, base.arg_names[i])
            arg_types.append(AnyType(TypeOfAny.suggestion_engine))
            # if (all_arg_types
            #         and all(isinstance(get_proper_type(tp), NoneType) for tp in all_arg_types)):
            #     arg_types.append(
            #         UnionType.make_union([all_arg_types[0], AnyType(TypeOfAny.explicit)]))
            # elif all_arg_types:
            #     arg_types.extend(generate_type_combinations(all_arg_types))
            # else:
            #     arg_types.append(AnyType(TypeOfAny.explicit))
            #     # This is a meet because the type needs to be compatible with all the uses
            #     arg_types.append(meet_type_list(all_use_types))
            
            # arg_types.extend(attr_type)
            if len(callable_recording[i]) > 0: 
                for typ in learnt[0]:
                    # Collect all the types except for implicit anys
                    if not is_implicit_any(typ):
                        arg_types = [typ]

            types.append(arg_types)

        return types

    def get_default_arg_types(self, state: State, fdef: FuncDef) -> List[Optional[Type]]:
        return [self.manager.all_types[arg.initializer] if arg.initializer else None
                for arg in fdef.arguments]

    def add_adjustments(self, typs: List[Type]) -> List[Type]:
        if not self.try_text or self.manager.options.python_version[0] != 2:
            return typs
        translator = StrToText(self.builtin_type)
        return dedup(typs + [tp.accept(translator) for tp in typs])
    def get_options(self, is_method: bool, base: CallableType, defaults: List[Optional[Type]],
                    callsites: List[Callsite],
                    uses: List[List[Type]], learnt: List[List[Type]], current_pos=None, user_types=None, attrs=None, callable_recording=None, arg_types_union=None):
        options = self.get_args(is_method, base, defaults, callsites, uses, learnt, current_pos, user_types, attrs, callable_recording, arg_types_union)
        options = [self.add_adjustments(tps) for tps in options]
        return options  
    def get_guesses(self, is_method: bool, base: CallableType, defaults: List[Optional[Type]],
                    callsites: List[Callsite],
                    uses: List[List[Type]], learnt: List[List[Type]], current_pos=None, user_types=None, attrs=None, callable_recording=None, arg_types_union=None) -> List[CallableType]:
        """Compute a list of guesses for a function's type.

        This focuses just on the argument types, and doesn't change the provided return type.
        """
        options = self.get_args(is_method, base, defaults, callsites, uses, learnt, current_pos, user_types, attrs, callable_recording, arg_types_union)
        options = [self.add_adjustments(tps) for tps in options]

        # Take the first `max_guesses` guesses.
        product = itertools.islice(itertools.product(*options), 0, self.max_guesses)
        return [refine_callable(base, base.copy_modified(arg_types=list(x))) for x in product]

    def get_callsites(self, func: FuncDef) -> Tuple[List[Callsite], List[str]]:
        """Find all call sites of a function."""
        new_type = self.get_starting_type(func)

        collector_plugin = SuggestionPlugin(func.fullname)

        self.plugin._plugins.insert(0, collector_plugin)
        try:
            errors = self.try_type(func, new_type)
        finally:
            self.plugin._plugins.pop(0)

        return collector_plugin.mystery_hits, errors
    
    def filter_options(
        self, guesses: List[CallableType], is_method: bool, ignore_return: bool
    ) -> List[CallableType]:
        """Apply any configured filters to the possible guesses.

        Currently the only option is filtering based on Any prevalance."""
        return [
            t for t in guesses
            if self.flex_any is None
            or any_score_callable(t, is_method, ignore_return) >= self.flex_any
        ]

    def find_best(self, func: FuncDef, guesses: List[CallableType], uses, global_type_map, global_incompatible, options, identity) -> Tuple[CallableType, int]:
        """From a list of possible function types, find the best one.

        For best, we want the fewest errors, then the best "score" from score_callable.
        """
        if not guesses:
            raise SuggestionFailure("No guesses that match criteria!")
        errors = {}
        self.all_times = 0
        baseline = self.try_type(func, guesses[-1])
        errors[guesses[-1]] = baseline
        best = guesses[-1]
        correct = {}
        correct[len(guesses)-1] = True
        for i, guess in enumerate(guesses[:-1]):
            # if self.all_times >= 100:
            #     break
            print(guess)
            now_typ = options[i]
            id_pair = (identity, now_typ)
            errors[guess] = self.try_type(func, guess, global_type_map, global_incompatible, id_pair)
            
            for err in errors[guess]:
                print(err)
            e = count_errors(errors[guess], baseline)
            
            if e < 10000000 and errors[guess][-1] == '0':
                best = guess
                correct[i] = True
            else:
                correct[i] = True # todo  False
        # errors = {guess: self.try_type(func, guess) for guess in guesses}
        # best = min(guesses,
        #            key=lambda s: (count_errors(errors[s], errors[guesses[-1]]), self.score_callable(s, uses)))
        if best:
            for i, arg_name in enumerate(func.arg_names):
                if self.memory.get(arg_name, None) is None:
                    self.memory[arg_name] = []
                self.memory[arg_name].append(best.arg_types[i])
            return best, count_errors(errors[best]), correct


    def get_guesses_from_parent(self, node: FuncDef) -> List[CallableType]:
        """Try to get a guess of a method type from a parent class."""
        if not node.info:
            return []

        for parent in node.info.mro[1:]:
            pnode = parent.names.get(node.name)
            if pnode and isinstance(pnode.node, (FuncDef, Decorator)):
                typ = get_proper_type(pnode.node.type)
                # FIXME: Doesn't work right with generic tyeps
                if isinstance(typ, CallableType) and len(typ.arg_types) == len(node.arguments):
                    # Return the first thing we find, since it probably doesn't make sense
                    # to grab things further up in the chain if an earlier parent has it.
                    return [typ]

        return []       
    def get_suggestion_On(self, mod: str, node: FuncDef, user_types, global_type_map, global_incompatible) -> PyAnnotateSignature:
        """Compute a suggestion for a function.

        Return the type and whether the first argument should be ignored.
        """
        finder = AssignFinder(node)
        node.body.accept(finder)
        graph = self.graph
        # todo define user_types elsewhere
        
        
        # try:
        #     
        #     graph_nodes = list(graph[mod]._type_checker.type_map.keys())
        # except Exception:
        #     graph_nodes = []
        Dgraph = DependencyGraph(node, self.graph[mod])
        order = Dgraph.typo_order
        vars = [x.variable for x in node.arguments]
        print(node.fullname)
        for current_node in order:
            
            current_pos = vars.index(current_node)
            
            callsites, orig_errors = self.get_callsites(node)
            # uses, attrs = get_arg_uses(self.manager.all_types, self.changed_func, node)
            uses, attrs, callable_recording, arg_types_union = get_arg_global_uses(self.manager.all_types, self.changed_func, node, graph[mod].tree, finder.assigns)
            i = current_pos
            print(str(i) + ': ' + str(uses[i]) + ' ' + str(attrs[i]) + ' ' + str(arg_types_union[i]))
            if self.no_errors and orig_errors:
                raise SuggestionFailure("Function does not typecheck.")

            is_method = bool(node.info) and not node.is_static
            
            types = list(self.manager.all_types.values())
            # graph[mod].type_check_first_pass()
            
            callable_type = CallableType([AnyType(TypeOfAny.explicit),
                                      AnyType(TypeOfAny.explicit)],
                                     [nodes.ARG_STAR, nodes.ARG_STAR2],
                                     [None, None],
                                     ret_type=AnyType(TypeOfAny.explicit),
                                     fallback=graph[mod]._type_checker.named_type('builtins.function'),
                                     is_ellipsis_args=True)
            
            
            learnt = [[callable_type], []]
            with strict_optional_set(graph[mod].options.strict_optional):
                base = self.get_starting_type(node)
                defaults = self.get_default_arg_types(graph[mod], node)
                options = self.get_options(
                    is_method,
                    self.get_starting_type(node),
                    self.get_default_arg_types(graph[mod], node),
                    callsites,
                    uses,
                    learnt, current_pos, user_types, attrs, callable_recording, arg_types_union
                )
                product = itertools.islice(itertools.product(*options), 0, self.max_guesses)
                guesses = [refine_callable(base, base.copy_modified(arg_types=list(x))) for x in product]
            
            identity = node.fullname + ':' + str(current_node.line) + ':' + current_node.fullname
            guesses += self.get_guesses_from_parent(node)
            guesses = self.filter_options(guesses, is_method, ignore_return=True)
            best, _, correct = self.find_best(node, guesses, uses, global_type_map, global_incompatible, options[current_pos], identity)
            unions = []
            global_type_map[identity] = []
            for i, candidate in enumerate(options[current_pos]):
                if correct[i] and i != len(guesses) -1:
                    unions.append(candidate)
                    global_type_map[identity].append(candidate)
            union_type = UnionType.make_union(unions)
            options[current_pos] = [union_type]
            product = itertools.islice(itertools.product(*options), 0, self.max_guesses)
            best = [refine_callable(base, base.copy_modified(arg_types=list(x))) for x in product][0]
            # Now try to find the return type!
            self.try_type(node, best)
            returns = get_return_types(self.manager.all_types, node)
            with strict_optional_set(graph[mod].options.strict_optional):
                if returns:
                    ret_types = generate_type_combinations(returns)
                else:
                    ret_types = [NoneType()]
            # print(mod)
            guesses = [best.copy_modified(ret_type=refine_type(best.ret_type, t)) for t in ret_types]
            guesses = self.filter_options(guesses, is_method, ignore_return=False)
            best, errors, correct = self.find_best(node, guesses, uses, global_type_map, global_incompatible, options[current_pos], identity)
            node.unanalyzed_type = best
            self.changed_func[node] = best
            if self.no_errors and errors:
                raise SuggestionFailure("No annotation without errors")

        return self.pyannotate_signature(mod, is_method, best)
    def get_suggestion(self, mod: str, node: FuncDef) -> PyAnnotateSignature:
        """Compute a suggestion for a function.

        Return the type and whether the first argument should be ignored.
        """
        graph = DependencyGraph(node)
        order = graph.typo_order
        while True:
            graph = self.graph
            callsites, orig_errors = self.get_callsites(node)
            uses = get_arg_uses(self.manager.all_types, self.changed_func, node)

            if self.no_errors and orig_errors:
                raise SuggestionFailure("Function does not typecheck.")

            is_method = bool(node.info) and not node.is_static
            
            types = list(self.manager.all_types.values())
            learnt = [[types[51]], []]
            with strict_optional_set(graph[mod].options.strict_optional):
                options = self.get_options(
                    is_method,
                    self.get_starting_type(node),
                    self.get_default_arg_types(graph[mod], node),
                    callsites,
                    uses,
                    learnt
                )
                product = itertools.islice(itertools.product(*options), 0, self.max_guesses)
                guesses = [refine_callable(base, base.copy_modified(arg_types=list(x))) for x in product]
            
            guesses += self.get_guesses_from_parent(node)
            guesses = self.filter_options(guesses, is_method, ignore_return=True)
            best, _, correct = self.find_best(node, guesses, uses)

            # Now try to find the return type!
            self.try_type(node, best)
            returns = get_return_types(self.manager.all_types, node)
            with strict_optional_set(graph[mod].options.strict_optional):
                if returns:
                    ret_types = generate_type_combinations(returns)
                else:
                    ret_types = [NoneType()]

            guesses = [best.copy_modified(ret_type=refine_type(best.ret_type, t)) for t in ret_types]
            guesses = self.filter_options(guesses, is_method, ignore_return=False)
            best, errors = self.find_best(node, guesses)
            node.unanalyzed_type = best
            self.changed_func[node] = best
            if self.no_errors and errors:
                raise SuggestionFailure("No annotation without errors")

        return self.pyannotate_signature(mod, is_method, best)

    def format_args(self,
                    arg_kinds: List[List[ArgKind]],
                    arg_names: List[List[Optional[str]]],
                    arg_types: List[List[Type]]) -> str:
        args: List[str] = []
        for i in range(len(arg_types)):
            for kind, name, typ in zip(arg_kinds[i], arg_names[i], arg_types[i]):
                arg = self.format_type(None, typ)
                if kind == ARG_STAR:
                    arg = '*' + arg
                elif kind == ARG_STAR2:
                    arg = '**' + arg
                elif kind.is_named():
                    if name:
                        arg = "%s=%s" % (name, arg)
            args.append(arg)
        return "(%s)" % (", ".join(args))

    def find_node(self, key: str) -> Tuple[str, str, FuncDef]:
        """From a target name, return module/target names and the func def.

        The 'key' argument can be in one of two formats:
        * As the function full name, e.g., package.module.Cls.method
        * As the function location as file and line separated by column,
          e.g., path/to/file.py:42
        """
        # TODO: Also return OverloadedFuncDef -- currently these are ignored.
        node: Optional[SymbolNode] = None
        if ':' in key:
            if key.count(':') > 1:
                raise SuggestionFailure(
                    'Malformed location for function: {}. Must be either'
                    ' package.module.Class.method or path/to/file.py:line'.format(key))
            file, line = key.split(':')
            if not line.isdigit():
                raise SuggestionFailure('Line number must be a number. Got {}'.format(line))
            line_number = int(line)
            modname, node = self.find_node_by_file_and_line(file, line_number)
            tail = node.fullname[len(modname) + 1:]  # add one to account for '.'
        else:
            target = split_target(self.fgmanager.graph, key)
            if not target:
                raise SuggestionFailure("Cannot find module for %s" % (key,))
            modname, tail = target
            node = self.find_node_by_module_and_name(modname, tail)

        if isinstance(node, Decorator):
            node = self.extract_from_decorator(node)
            if not node:
                raise SuggestionFailure("Object %s is a decorator we can't handle" % key)

        if not isinstance(node, FuncDef):
            raise SuggestionFailure("Object %s is not a function" % key)

        return modname, tail, node

    def find_node_by_module_and_name(self, modname: str, tail: str) -> Optional[SymbolNode]:
        """Find symbol node by module id and qualified name.

        Raise SuggestionFailure if can't find one.
        """
        if not self.tree:
            self.tree = self.ensure_loaded(self.fgmanager.graph[modname], True)
        tree = self.tree
        # N.B. This is reimplemented from update's lookup_target
        # basically just to produce better error messages.

        names: SymbolTable = tree.names

        # Look through any classes
        components = tail.split('.')
        for i, component in enumerate(components[:-1]):
            if component not in names:
                raise SuggestionFailure("Unknown class %s.%s" %
                                        (modname, '.'.join(components[:i + 1])))
            node: Optional[SymbolNode] = names[component].node
            if not isinstance(node, TypeInfo):
                raise SuggestionFailure("Object %s.%s is not a class" %
                                        (modname, '.'.join(components[:i + 1])))
            names = node.names

        # Look for the actual function/method
        funcname = components[-1]
        if funcname not in names:
            key = modname + '.' + tail
            raise SuggestionFailure("Unknown %s %s" %
                                    ("method" if len(components) > 1 else "function", key))
        return names[funcname].node

    def find_node_by_file_and_line(self, file: str, line: int) -> Tuple[str, SymbolNode]:
        """Find symbol node by path to file and line number.

        Find the first function declared *before or on* the line number.

        Return module id and the node found. Raise SuggestionFailure if can't find one.
        """
        if not any(file.endswith(ext) for ext in PYTHON_EXTENSIONS):
            raise SuggestionFailure('Source file is not a Python file')
        try:
            modname, _ = self.finder.crawl_up(os.path.normpath(file))
        except InvalidSourceList as e:
            raise SuggestionFailure('Invalid source file name: ' + file) from e
        if modname not in self.graph:
            raise SuggestionFailure('Unknown module: ' + modname)
        # We must be sure about any edits in this file as this might affect the line numbers.
        tree = self.ensure_loaded(self.fgmanager.graph[modname], force=True)
        node: Optional[SymbolNode] = None
        closest_line: Optional[int] = None
        # TODO: Handle nested functions.
        for _, sym, _ in tree.local_definitions():
            if isinstance(sym.node, (FuncDef, Decorator)):
                sym_line = sym.node.line
            # TODO: add support for OverloadedFuncDef.
            else:
                continue

            # We want the closest function above the specified line
            if sym_line <= line and (closest_line is None or sym_line > closest_line):
                closest_line = sym_line
                node = sym.node
        if not node:
            raise SuggestionFailure('Cannot find a function at line {}'.format(line))
        return modname, node

    def extract_from_decorator(self, node: Decorator) -> Optional[FuncDef]:
        for dec in node.decorators:
            typ = None
            if (isinstance(dec, RefExpr)
                    and isinstance(dec.node, FuncDef)):
                typ = dec.node.type
            elif (isinstance(dec, CallExpr)
                    and isinstance(dec.callee, RefExpr)
                    and isinstance(dec.callee.node, FuncDef)
                    and isinstance(dec.callee.node.type, CallableType)):
                typ = get_proper_type(dec.callee.node.type.ret_type)

            if not isinstance(typ, FunctionLike):
                return None
            for ct in typ.items:
                if not (len(ct.arg_types) == 1
                        and isinstance(ct.arg_types[0], TypeVarType)
                        and ct.arg_types[0] == ct.ret_type):
                    return None

        return node.func

    def try_type(self, func: FuncDef, typ: ProperType, global_type_map=None, global_incompatible=None, id_pair=None) -> List[str]:
        """Recheck a function while assuming it has type typ.

        Return all error messages.
        """
        t0 = time.time()
        old = func.unanalyzed_type
        # During reprocessing, unanalyzed_type gets copied to type (by aststrip).
        # We set type to None to ensure that the type always changes during
        # reprocessing.
        func.type = None
        func.unanalyzed_type = typ
        
        try:
            res = self.fgmanager.trigger(func.fullname, global_type_map, global_incompatible, id_pair)
            t1 = time.time()
            delta = t1 - t0 
            self.all_times += delta
            # if res:
            #     # print('===', typ)
            #     # print('\n'.join(res))
            return res
            
        finally:
            func.unanalyzed_type = old

    def reload(self, state: State, check_errors: bool = False) -> List[str]:
        """Recheck the module given by state.

        If check_errors is true, raise an exception if there are errors.
        """
        assert state.path is not None
        self.fgmanager.flush_cache()
        return self.fgmanager.update([(state.id, state.path)], [])

    def ensure_loaded(self, state: State, force: bool = False) -> MypyFile:
        """Make sure that the module represented by state is fully loaded."""
        if not state.tree or state.tree.is_cache_skeleton or force:
            self.reload(state)
        assert state.tree is not None
        return state.tree

    def builtin_type(self, s: str) -> Instance:
        return self.manager.semantic_analyzer.builtin_type(s)

    def json_suggestion(self, mod: str, func_name: str, node: FuncDef,
                        suggestion: PyAnnotateSignature) -> str:
        """Produce a json blob for a suggestion suitable for application by pyannotate."""
        # pyannotate irritatingly drops class names for class and static methods
        if node.is_class or node.is_static:
            func_name = func_name.split('.', 1)[-1]

        # pyannotate works with either paths relative to where the
        # module is rooted or with absolute paths. We produce absolute
        # paths because it is simpler.
        path = os.path.abspath(self.graph[mod].xpath)

        obj = {
            'signature': suggestion,
            'line': node.line,
            'path': path,
            'func_name': func_name,
            'samples': 0
        }
        return json.dumps([obj], sort_keys=True)

    def pyannotate_signature(
        self,
        cur_module: Optional[str],
        is_method: bool,
        typ: CallableType
    ) -> PyAnnotateSignature:
        """Format a callable type as a pyannotate dict"""
        start = int(is_method)
        return {
            'arg_types': [self.format_type(cur_module, t) for t in typ.arg_types[start:]],
            'return_type': self.format_type(cur_module, typ.ret_type),
        }

    def format_signature(self, sig: PyAnnotateSignature) -> str:
        """Format a callable type in a way suitable as an annotation... kind of"""
        return "({}) -> {}".format(
            ", ".join(sig['arg_types']),
            sig['return_type']
        )

    def format_type(self, cur_module: Optional[str], typ: Type) -> str:
        if self.use_fixme and isinstance(get_proper_type(typ), AnyType):
            return self.use_fixme
        return typ.accept(TypeFormatter(cur_module, self.graph))

    def score_type(self, t: Type, arg_pos: bool) -> int:
        """Generate a score for a type that we use to pick which type to use.

        Lower is better, prefer non-union/non-any types. Don't penalize optionals.
        """
        t = get_proper_type(t)
        if isinstance(t, AnyType):
            return 20
        if arg_pos and isinstance(t, NoneType):
            return 20
        if isinstance(t, UnionType):
            if any(isinstance(get_proper_type(x), AnyType) for x in t.items):
                return 20
            if any(has_any_type(x) for x in t.items):
                return 15
            if not is_optional(t):
                return 10
        if isinstance(t, CallableType) and (has_any_type(t) or is_tricky_callable(t)):
            return 10
        if is_optional(t):
            return 10
        if self.try_text and isinstance(t, Instance) and t.type.fullname == 'builtins.str':
            return 1
        return 0

    def score_callable(self, t: CallableType, uses) -> int:
        return (sum([self.score_type(x, arg_pos=True) for x in t.arg_types]) +
                self.score_type(t.ret_type, arg_pos=False))


def any_score_type(ut: Type, arg_pos: bool) -> float:
    """Generate a very made up number representing the Anyness of a type.

    Higher is better, 1.0 is max
    """
    t = get_proper_type(ut)
    if isinstance(t, AnyType) and t.type_of_any != TypeOfAny.suggestion_engine:
        return 0
    if isinstance(t, NoneType) and arg_pos:
        return 0.5
    if isinstance(t, UnionType):
        if any(isinstance(get_proper_type(x), AnyType) for x in t.items):
            return 0.5
        if any(has_any_type(x) for x in t.items):
            return 0.25
    if isinstance(t, CallableType) and is_tricky_callable(t):
        return 0.5
    if has_any_type(t):
        return 0.5

    return 1.0


def any_score_callable(t: CallableType, is_method: bool, ignore_return: bool) -> float:
    # Ignore the first argument of methods
    scores = [any_score_type(x, arg_pos=True) for x in t.arg_types[int(is_method):]]
    # Return type counts twice (since it spreads type information), unless it is
    # None in which case it does not count at all. (Though it *does* still count
    # if there are no arguments.)
    if not isinstance(get_proper_type(t.ret_type), NoneType) or not scores:
        ret = 1.0 if ignore_return else any_score_type(t.ret_type, arg_pos=False)
        scores += [ret, ret]

    return sum(scores) / len(scores)


def is_tricky_callable(t: CallableType) -> bool:
    """Is t a callable that we need to put a ... in for syntax reasons?"""
    return t.is_ellipsis_args or any(k.is_star() or k.is_named() for k in t.arg_kinds)


class TypeFormatter(TypeStrVisitor):
    """Visitor used to format types
    """
    # TODO: Probably a lot
    def __init__(self, module: Optional[str], graph: Graph) -> None:
        super().__init__()
        self.module = module
        self.graph = graph

    def visit_any(self, t: AnyType) -> str:
        if t.missing_import_name:
            return t.missing_import_name
        else:
            return "Any"

    def visit_instance(self, t: Instance) -> str:
        s = t.type.fullname or t.type.name or None
        if s is None:
            return '<???>'
        if s in reverse_builtin_aliases:
            s = reverse_builtin_aliases[s]

        mod_obj = split_target(self.graph, s)
        assert mod_obj
        mod, obj = mod_obj

        # If a class is imported into the current module, rewrite the reference
        # to point to the current module. This helps the annotation tool avoid
        # inserting redundant imports when a type has been reexported.
        if self.module:
            parts = obj.split('.')  # need to split the object part if it is a nested class
            tree = self.graph[self.module].tree
            if tree and parts[0] in tree.names:
                mod = self.module

        if (mod, obj) == ('builtins', 'tuple'):
            mod, obj = 'typing', 'Tuple[' + t.args[0].accept(self) + ', ...]'
        elif t.args:
            obj += '[{}]'.format(self.list_str(t.args))

        if mod_obj == ('builtins', 'unicode'):
            return 'Text'
        elif mod == 'builtins':
            return obj
        else:
            delim = '.' if '.' not in obj else ':'
            return mod + delim + obj

    def visit_tuple_type(self, t: TupleType) -> str:
        if t.partial_fallback and t.partial_fallback.type:
            fallback_name = t.partial_fallback.type.fullname
            if fallback_name != 'builtins.tuple':
                return t.partial_fallback.accept(self)
        s = self.list_str(t.items)
        return 'Tuple[{}]'.format(s)

    def visit_uninhabited_type(self, t: UninhabitedType) -> str:
        return "Any"

    def visit_typeddict_type(self, t: TypedDictType) -> str:
        return t.fallback.accept(self)

    def visit_union_type(self, t: UnionType) -> str:
        if len(t.items) == 2 and is_optional(t):
            return "Optional[{}]".format(remove_optional(t).accept(self))
        else:
            return super().visit_union_type(t)

    def visit_callable_type(self, t: CallableType) -> str:
        # TODO: use extended callables?
        if is_tricky_callable(t):
            arg_str = "..."
        else:
            # Note: for default arguments, we just assume that they
            # are required.  This isn't right, but neither is the
            # other thing, and I suspect this will produce more better
            # results than falling back to `...`
            args = [typ.accept(self) for typ in t.arg_types]
            arg_str = "[{}]".format(", ".join(args))

        return "Callable[{}, {}]".format(arg_str, t.ret_type.accept(self))


class StrToText(TypeTranslator):
    def __init__(self, builtin_type: Callable[[str], Instance]) -> None:
        self.text_type = builtin_type('builtins.unicode')

    def visit_type_alias_type(self, t: TypeAliasType) -> Type:
        exp_t = get_proper_type(t)
        if isinstance(exp_t, Instance) and exp_t.type.fullname == 'builtins.str':
            return self.text_type
        return t.copy_modified(args=[a.accept(self) for a in t.args])

    def visit_instance(self, t: Instance) -> Type:
        if t.type.fullname == 'builtins.str':
            return self.text_type
        else:
            return super().visit_instance(t)


TType = TypeVar('TType', bound=Type)


def make_suggestion_anys(t: TType) -> TType:
    """Make all anys in the type as coming from the suggestion engine.

    This keeps those Anys from influencing constraint generation,
    which allows us to do better when refining types.
    """
    return cast(TType, t.accept(MakeSuggestionAny()))


class MakeSuggestionAny(TypeTranslator):
    def visit_any(self, t: AnyType) -> Type:
        if not t.missing_import_name:
            return t.copy_modified(type_of_any=TypeOfAny.suggestion_engine)
        else:
            return t

    def visit_type_alias_type(self, t: TypeAliasType) -> Type:
        return t.copy_modified(args=[a.accept(self) for a in t.args])


def generate_type_combinations(types: List[Type]) -> List[Type]:
    """Generate possible combinations of a list of types.

    mypy essentially supports two different ways to do this: joining the types
    and unioning the types. We try both.
    """
    joined_type = join_type_list(types)
    union_type = make_simplified_union(types)
    if is_same_type(joined_type, union_type):
        return [joined_type]
    else:
        return [joined_type, union_type]


def count_errors(msgs: List[str], baseline=None) -> int:
    if baseline is not None:

        lineos = [x.split('.py:')[1].split(': error')[0] for x in baseline]
        for msg in msgs[:-1]:
            if msg not in baseline:
                linen = msg.split('.py:')[1].split(': error')[0]
                if linen not in lineos:
                    return 10000000
    return len([x for x in msgs if ' error: ' in x])


def refine_type(ti: Type, si: Type) -> Type:
    """Refine `ti` by replacing Anys in it with information taken from `si`

    This basically works by, when the types have the same structure,
    traversing both of them in parallel and replacing Any on the left
    with whatever the type on the right is. If the types don't have the
    same structure (or aren't supported), the left type is chosen.

    For example:
      refine(Any, T) = T,  for all T
      refine(float, int) = float
      refine(List[Any], List[int]) = List[int]
      refine(Dict[int, Any], Dict[Any, int]) = Dict[int, int]
      refine(Tuple[int, Any], Tuple[Any, int]) = Tuple[int, int]

      refine(Callable[[Any], Any], Callable[[int], int]) = Callable[[int], int]
      refine(Callable[..., int], Callable[[int, float], Any]) = Callable[[int, float], int]

      refine(Optional[Any], int) = Optional[int]
      refine(Optional[Any], Optional[int]) = Optional[int]
      refine(Optional[Any], Union[int, str]) = Optional[Union[int, str]]
      refine(Optional[List[Any]], List[int]) = List[int]

    """
    t = get_proper_type(ti)
    s = get_proper_type(si)

    if isinstance(t, AnyType):
        # If s is also an Any, we return if it is a missing_import Any
        return t if isinstance(s, AnyType) and t.missing_import_name else s

    if isinstance(t, Instance) and isinstance(s, Instance) and t.type == s.type:
        return t.copy_modified(args=[refine_type(ta, sa) for ta, sa in zip(t.args, s.args)])

    if (
        isinstance(t, TupleType)
        and isinstance(s, TupleType)
        and t.partial_fallback == s.partial_fallback
        and len(t.items) == len(s.items)
    ):
        return t.copy_modified(items=[refine_type(ta, sa) for ta, sa in zip(t.items, s.items)])

    if isinstance(t, CallableType) and isinstance(s, CallableType):
        return refine_callable(t, s)

    if isinstance(t, UnionType):
        return refine_union(t, s)

    # TODO: Refining of builtins.tuple, Type?

    return t


def refine_union(t: UnionType, s: ProperType) -> Type:
    """Refine a union type based on another type.

    This is done by refining every component of the union against the
    right hand side type (or every component of its union if it is
    one). If an element of the union is successfully refined, we drop it
    from the union in favor of the refined versions.
    """
    # Don't try to do any union refining if the types are already the
    # same.  This prevents things like refining Optional[Any] against
    # itself and producing None.
    if t == s:
        return t

    rhs_items = s.items if isinstance(s, UnionType) else [s]

    new_items = []
    for lhs in t.items:
        refined = False
        for rhs in rhs_items:
            new = refine_type(lhs, rhs)
            if new != lhs:
                new_items.append(new)
                refined = True
        if not refined:
            new_items.append(lhs)

    # Turn strict optional on when simplifying the union since we
    # don't want to drop Nones.
    with strict_optional_set(True):
        return make_simplified_union(new_items)


def refine_callable(t: CallableType, s: CallableType) -> CallableType:
    """Refine a callable based on another.

    See comments for refine_type.
    """
    if t.fallback != s.fallback:
        return t

    if t.is_ellipsis_args and not is_tricky_callable(s):
        return s.copy_modified(ret_type=refine_type(t.ret_type, s.ret_type))
    # if star, do not substitute
    if (is_tricky_callable(t) or t.arg_kinds != s.arg_kinds) and not is_tricky_callable(s):
        return t

    return t.copy_modified(
        arg_types=[refine_type(ta, sa) for ta, sa in zip(t.arg_types, s.arg_types)],
        ret_type=refine_type(t.ret_type, s.ret_type),
    )


T = TypeVar('T')


def dedup(old: List[T]) -> List[T]:
    new: List[T] = []
    for x in old:
        if x not in new:
            new.append(x)
    return new
