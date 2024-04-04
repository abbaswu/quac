"""Generic abstract syntax tree node visitor"""

from abc import abstractmethod
from typing import TypeVar, Generic
from typing_extensions import TYPE_CHECKING
from mypy_extensions import trait, mypyc_attr

if TYPE_CHECKING:
    # break import cycle only needed for mypy
    import extyper.nodes


T = TypeVar('T')


@trait
@mypyc_attr(allow_interpreted_subclasses=True)
class ExpressionVisitor(Generic[T]):
    @abstractmethod
    def visit_int_expr(self, o: 'extyper.nodes.IntExpr') -> T:
        pass

    @abstractmethod
    def visit_str_expr(self, o: 'extyper.nodes.StrExpr') -> T:
        pass

    @abstractmethod
    def visit_bytes_expr(self, o: 'extyper.nodes.BytesExpr') -> T:
        pass

    @abstractmethod
    def visit_unicode_expr(self, o: 'extyper.nodes.UnicodeExpr') -> T:
        pass

    @abstractmethod
    def visit_float_expr(self, o: 'extyper.nodes.FloatExpr') -> T:
        pass

    @abstractmethod
    def visit_complex_expr(self, o: 'extyper.nodes.ComplexExpr') -> T:
        pass

    @abstractmethod
    def visit_ellipsis(self, o: 'extyper.nodes.EllipsisExpr') -> T:
        pass

    @abstractmethod
    def visit_star_expr(self, o: 'extyper.nodes.StarExpr') -> T:
        pass

    @abstractmethod
    def visit_name_expr(self, o: 'extyper.nodes.NameExpr') -> T:
        pass

    @abstractmethod
    def visit_member_expr(self, o: 'extyper.nodes.MemberExpr') -> T:
        pass

    @abstractmethod
    def visit_yield_from_expr(self, o: 'extyper.nodes.YieldFromExpr') -> T:
        pass

    @abstractmethod
    def visit_yield_expr(self, o: 'extyper.nodes.YieldExpr') -> T:
        pass

    @abstractmethod
    def visit_call_expr(self, o: 'extyper.nodes.CallExpr') -> T:
        pass

    @abstractmethod
    def visit_op_expr(self, o: 'extyper.nodes.OpExpr') -> T:
        pass

    @abstractmethod
    def visit_comparison_expr(self, o: 'extyper.nodes.ComparisonExpr') -> T:
        pass

    @abstractmethod
    def visit_cast_expr(self, o: 'extyper.nodes.CastExpr') -> T:
        pass

    @abstractmethod
    def visit_reveal_expr(self, o: 'extyper.nodes.RevealExpr') -> T:
        pass

    @abstractmethod
    def visit_super_expr(self, o: 'extyper.nodes.SuperExpr') -> T:
        pass

    @abstractmethod
    def visit_unary_expr(self, o: 'extyper.nodes.UnaryExpr') -> T:
        pass

    @abstractmethod
    def visit_assignment_expr(self, o: 'extyper.nodes.AssignmentExpr') -> T:
        pass

    @abstractmethod
    def visit_list_expr(self, o: 'extyper.nodes.ListExpr') -> T:
        pass

    @abstractmethod
    def visit_dict_expr(self, o: 'extyper.nodes.DictExpr') -> T:
        pass

    @abstractmethod
    def visit_tuple_expr(self, o: 'extyper.nodes.TupleExpr') -> T:
        pass

    @abstractmethod
    def visit_set_expr(self, o: 'extyper.nodes.SetExpr') -> T:
        pass

    @abstractmethod
    def visit_index_expr(self, o: 'extyper.nodes.IndexExpr') -> T:
        pass

    @abstractmethod
    def visit_type_application(self, o: 'extyper.nodes.TypeApplication') -> T:
        pass

    @abstractmethod
    def visit_lambda_expr(self, o: 'extyper.nodes.LambdaExpr') -> T:
        pass

    @abstractmethod
    def visit_list_comprehension(self, o: 'extyper.nodes.ListComprehension') -> T:
        pass

    @abstractmethod
    def visit_set_comprehension(self, o: 'extyper.nodes.SetComprehension') -> T:
        pass

    @abstractmethod
    def visit_dictionary_comprehension(self, o: 'extyper.nodes.DictionaryComprehension') -> T:
        pass

    @abstractmethod
    def visit_generator_expr(self, o: 'extyper.nodes.GeneratorExpr') -> T:
        pass

    @abstractmethod
    def visit_slice_expr(self, o: 'extyper.nodes.SliceExpr') -> T:
        pass

    @abstractmethod
    def visit_conditional_expr(self, o: 'extyper.nodes.ConditionalExpr') -> T:
        pass

    @abstractmethod
    def visit_backquote_expr(self, o: 'extyper.nodes.BackquoteExpr') -> T:
        pass

    @abstractmethod
    def visit_type_var_expr(self, o: 'extyper.nodes.TypeVarExpr') -> T:
        pass

    @abstractmethod
    def visit_paramspec_expr(self, o: 'extyper.nodes.ParamSpecExpr') -> T:
        pass

    @abstractmethod
    def visit_type_alias_expr(self, o: 'extyper.nodes.TypeAliasExpr') -> T:
        pass

    @abstractmethod
    def visit_namedtuple_expr(self, o: 'extyper.nodes.NamedTupleExpr') -> T:
        pass

    @abstractmethod
    def visit_enum_call_expr(self, o: 'extyper.nodes.EnumCallExpr') -> T:
        pass

    @abstractmethod
    def visit_typeddict_expr(self, o: 'extyper.nodes.TypedDictExpr') -> T:
        pass

    @abstractmethod
    def visit_newtype_expr(self, o: 'extyper.nodes.NewTypeExpr') -> T:
        pass

    @abstractmethod
    def visit__promote_expr(self, o: 'extyper.nodes.PromoteExpr') -> T:
        pass

    @abstractmethod
    def visit_await_expr(self, o: 'extyper.nodes.AwaitExpr') -> T:
        pass

    @abstractmethod
    def visit_temp_node(self, o: 'extyper.nodes.TempNode') -> T:
        pass


@trait
@mypyc_attr(allow_interpreted_subclasses=True)
class StatementVisitor(Generic[T]):
    # Definitions

    @abstractmethod
    def visit_assignment_stmt(self, o: 'extyper.nodes.AssignmentStmt') -> T:
        pass

    @abstractmethod
    def visit_for_stmt(self, o: 'extyper.nodes.ForStmt') -> T:
        pass

    @abstractmethod
    def visit_with_stmt(self, o: 'extyper.nodes.WithStmt') -> T:
        pass

    @abstractmethod
    def visit_del_stmt(self, o: 'extyper.nodes.DelStmt') -> T:
        pass

    @abstractmethod
    def visit_func_def(self, o: 'extyper.nodes.FuncDef') -> T:
        pass

    @abstractmethod
    def visit_overloaded_func_def(self, o: 'extyper.nodes.OverloadedFuncDef') -> T:
        pass

    @abstractmethod
    def visit_class_def(self, o: 'extyper.nodes.ClassDef') -> T:
        pass

    @abstractmethod
    def visit_global_decl(self, o: 'extyper.nodes.GlobalDecl') -> T:
        pass

    @abstractmethod
    def visit_nonlocal_decl(self, o: 'extyper.nodes.NonlocalDecl') -> T:
        pass

    @abstractmethod
    def visit_decorator(self, o: 'extyper.nodes.Decorator') -> T:
        pass

    # Module structure

    @abstractmethod
    def visit_import(self, o: 'extyper.nodes.Import') -> T:
        pass

    @abstractmethod
    def visit_import_from(self, o: 'extyper.nodes.ImportFrom') -> T:
        pass

    @abstractmethod
    def visit_import_all(self, o: 'extyper.nodes.ImportAll') -> T:
        pass

    # Statements

    @abstractmethod
    def visit_block(self, o: 'extyper.nodes.Block') -> T:
        pass

    @abstractmethod
    def visit_expression_stmt(self, o: 'extyper.nodes.ExpressionStmt') -> T:
        pass

    @abstractmethod
    def visit_operator_assignment_stmt(self, o: 'extyper.nodes.OperatorAssignmentStmt') -> T:
        pass

    @abstractmethod
    def visit_while_stmt(self, o: 'extyper.nodes.WhileStmt') -> T:
        pass

    @abstractmethod
    def visit_return_stmt(self, o: 'extyper.nodes.ReturnStmt') -> T:
        pass

    @abstractmethod
    def visit_assert_stmt(self, o: 'extyper.nodes.AssertStmt') -> T:
        pass

    @abstractmethod
    def visit_if_stmt(self, o: 'extyper.nodes.IfStmt') -> T:
        pass

    @abstractmethod
    def visit_break_stmt(self, o: 'extyper.nodes.BreakStmt') -> T:
        pass

    @abstractmethod
    def visit_continue_stmt(self, o: 'extyper.nodes.ContinueStmt') -> T:
        pass

    @abstractmethod
    def visit_pass_stmt(self, o: 'extyper.nodes.PassStmt') -> T:
        pass

    @abstractmethod
    def visit_raise_stmt(self, o: 'extyper.nodes.RaiseStmt') -> T:
        pass

    @abstractmethod
    def visit_try_stmt(self, o: 'extyper.nodes.TryStmt') -> T:
        pass

    @abstractmethod
    def visit_print_stmt(self, o: 'extyper.nodes.PrintStmt') -> T:
        pass

    @abstractmethod
    def visit_exec_stmt(self, o: 'extyper.nodes.ExecStmt') -> T:
        pass


@trait
@mypyc_attr(allow_interpreted_subclasses=True)
class NodeVisitor(Generic[T], ExpressionVisitor[T], StatementVisitor[T]):
    """Empty base class for parse tree node visitors.

    The T type argument specifies the return type of the visit
    methods. As all methods defined here return None by default,
    subclasses do not always need to override all the methods.

    TODO make the default return value explicit
    """

    # Not in superclasses:

    def visit_mypy_file(self, o: 'extyper.nodes.MypyFile') -> T:
        pass

    # TODO: We have a visit_var method, but no visit_typeinfo or any
    # other non-Statement SymbolNode (accepting those will raise a
    # runtime error). Maybe this should be resolved in some direction.
    def visit_var(self, o: 'extyper.nodes.Var') -> T:
        pass

    # Module structure

    def visit_import(self, o: 'extyper.nodes.Import') -> T:
        pass

    def visit_import_from(self, o: 'extyper.nodes.ImportFrom') -> T:
        pass

    def visit_import_all(self, o: 'extyper.nodes.ImportAll') -> T:
        pass

    # Definitions

    def visit_func_def(self, o: 'extyper.nodes.FuncDef') -> T:
        pass

    def visit_overloaded_func_def(self,
                                  o: 'extyper.nodes.OverloadedFuncDef') -> T:
        pass

    def visit_class_def(self, o: 'extyper.nodes.ClassDef') -> T:
        pass

    def visit_global_decl(self, o: 'extyper.nodes.GlobalDecl') -> T:
        pass

    def visit_nonlocal_decl(self, o: 'extyper.nodes.NonlocalDecl') -> T:
        pass

    def visit_decorator(self, o: 'extyper.nodes.Decorator') -> T:
        pass

    def visit_type_alias(self, o: 'extyper.nodes.TypeAlias') -> T:
        pass

    def visit_placeholder_node(self, o: 'extyper.nodes.PlaceholderNode') -> T:
        pass

    # Statements

    def visit_block(self, o: 'extyper.nodes.Block') -> T:
        pass

    def visit_expression_stmt(self, o: 'extyper.nodes.ExpressionStmt') -> T:
        pass

    def visit_assignment_stmt(self, o: 'extyper.nodes.AssignmentStmt') -> T:
        pass

    def visit_operator_assignment_stmt(self,
                                       o: 'extyper.nodes.OperatorAssignmentStmt') -> T:
        pass

    def visit_while_stmt(self, o: 'extyper.nodes.WhileStmt') -> T:
        pass

    def visit_for_stmt(self, o: 'extyper.nodes.ForStmt') -> T:
        pass

    def visit_return_stmt(self, o: 'extyper.nodes.ReturnStmt') -> T:
        pass

    def visit_assert_stmt(self, o: 'extyper.nodes.AssertStmt') -> T:
        pass

    def visit_del_stmt(self, o: 'extyper.nodes.DelStmt') -> T:
        pass

    def visit_if_stmt(self, o: 'extyper.nodes.IfStmt') -> T:
        pass

    def visit_break_stmt(self, o: 'extyper.nodes.BreakStmt') -> T:
        pass

    def visit_continue_stmt(self, o: 'extyper.nodes.ContinueStmt') -> T:
        pass

    def visit_pass_stmt(self, o: 'extyper.nodes.PassStmt') -> T:
        pass

    def visit_raise_stmt(self, o: 'extyper.nodes.RaiseStmt') -> T:
        pass

    def visit_try_stmt(self, o: 'extyper.nodes.TryStmt') -> T:
        pass

    def visit_with_stmt(self, o: 'extyper.nodes.WithStmt') -> T:
        pass

    def visit_print_stmt(self, o: 'extyper.nodes.PrintStmt') -> T:
        pass

    def visit_exec_stmt(self, o: 'extyper.nodes.ExecStmt') -> T:
        pass

    # Expressions (default no-op implementation)

    def visit_int_expr(self, o: 'extyper.nodes.IntExpr') -> T:
        pass

    def visit_str_expr(self, o: 'extyper.nodes.StrExpr') -> T:
        pass

    def visit_bytes_expr(self, o: 'extyper.nodes.BytesExpr') -> T:
        pass

    def visit_unicode_expr(self, o: 'extyper.nodes.UnicodeExpr') -> T:
        pass

    def visit_float_expr(self, o: 'extyper.nodes.FloatExpr') -> T:
        pass

    def visit_complex_expr(self, o: 'extyper.nodes.ComplexExpr') -> T:
        pass

    def visit_ellipsis(self, o: 'extyper.nodes.EllipsisExpr') -> T:
        pass

    def visit_star_expr(self, o: 'extyper.nodes.StarExpr') -> T:
        pass

    def visit_name_expr(self, o: 'extyper.nodes.NameExpr') -> T:
        pass

    def visit_member_expr(self, o: 'extyper.nodes.MemberExpr') -> T:
        pass

    def visit_yield_from_expr(self, o: 'extyper.nodes.YieldFromExpr') -> T:
        pass

    def visit_yield_expr(self, o: 'extyper.nodes.YieldExpr') -> T:
        pass

    def visit_call_expr(self, o: 'extyper.nodes.CallExpr') -> T:
        pass

    def visit_op_expr(self, o: 'extyper.nodes.OpExpr') -> T:
        pass

    def visit_comparison_expr(self, o: 'extyper.nodes.ComparisonExpr') -> T:
        pass

    def visit_cast_expr(self, o: 'extyper.nodes.CastExpr') -> T:
        pass

    def visit_reveal_expr(self, o: 'extyper.nodes.RevealExpr') -> T:
        pass

    def visit_super_expr(self, o: 'extyper.nodes.SuperExpr') -> T:
        pass

    def visit_assignment_expr(self, o: 'extyper.nodes.AssignmentExpr') -> T:
        pass

    def visit_unary_expr(self, o: 'extyper.nodes.UnaryExpr') -> T:
        pass

    def visit_list_expr(self, o: 'extyper.nodes.ListExpr') -> T:
        pass

    def visit_dict_expr(self, o: 'extyper.nodes.DictExpr') -> T:
        pass

    def visit_tuple_expr(self, o: 'extyper.nodes.TupleExpr') -> T:
        pass

    def visit_set_expr(self, o: 'extyper.nodes.SetExpr') -> T:
        pass

    def visit_index_expr(self, o: 'extyper.nodes.IndexExpr') -> T:
        pass

    def visit_type_application(self, o: 'extyper.nodes.TypeApplication') -> T:
        pass

    def visit_lambda_expr(self, o: 'extyper.nodes.LambdaExpr') -> T:
        pass

    def visit_list_comprehension(self, o: 'extyper.nodes.ListComprehension') -> T:
        pass

    def visit_set_comprehension(self, o: 'extyper.nodes.SetComprehension') -> T:
        pass

    def visit_dictionary_comprehension(self, o: 'extyper.nodes.DictionaryComprehension') -> T:
        pass

    def visit_generator_expr(self, o: 'extyper.nodes.GeneratorExpr') -> T:
        pass

    def visit_slice_expr(self, o: 'extyper.nodes.SliceExpr') -> T:
        pass

    def visit_conditional_expr(self, o: 'extyper.nodes.ConditionalExpr') -> T:
        pass

    def visit_backquote_expr(self, o: 'extyper.nodes.BackquoteExpr') -> T:
        pass

    def visit_type_var_expr(self, o: 'extyper.nodes.TypeVarExpr') -> T:
        pass

    def visit_paramspec_expr(self, o: 'extyper.nodes.ParamSpecExpr') -> T:
        pass

    def visit_type_alias_expr(self, o: 'extyper.nodes.TypeAliasExpr') -> T:
        pass

    def visit_namedtuple_expr(self, o: 'extyper.nodes.NamedTupleExpr') -> T:
        pass

    def visit_enum_call_expr(self, o: 'extyper.nodes.EnumCallExpr') -> T:
        pass

    def visit_typeddict_expr(self, o: 'extyper.nodes.TypedDictExpr') -> T:
        pass

    def visit_newtype_expr(self, o: 'extyper.nodes.NewTypeExpr') -> T:
        pass

    def visit__promote_expr(self, o: 'extyper.nodes.PromoteExpr') -> T:
        pass

    def visit_await_expr(self, o: 'extyper.nodes.AwaitExpr') -> T:
        pass

    def visit_temp_node(self, o: 'extyper.nodes.TempNode') -> T:
        pass
