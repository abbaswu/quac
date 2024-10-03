"""
In [1]: from client import *

In [2]: from type_annotation import *

In [3]: module_name = 'builtins'

In [4]: import importlib

In [5]: module = importlib.import_module(module_name)

In [6]: global_function_list = [ v for k, v in module.__dict__.items() if callable(v) and not isinstance(v, type) \
and v.__module__ == module_name]

In [7]: class_list = [ v for k, v in module.__dict__.items() if isinstance(v, type) and v.__module__ == module_name ]

In [8]: for f in global_function_list: look_up_function(GlobalFunction(f.__module__, f.__name__))

In [9]: for c in class_list: look_up_class(TypeshedClass(c.__module__, c.__name__))
"""

import ast
from inspect import currentframe, getframeinfo
from pathlib import Path
from typing import Optional, Union as tUnion

import networkx as nx
import typeshed_client.parser
from typeshed_client.finder import SearchContext, get_search_context

from .runtime_class_name_tuples_and_typeshed_class_name_tuples import runtime_class_name_tuple_to_typeshed_class_name_tuple
from .iterate_components_in_ast_attribute import iterate_components_in_ast_attribute
from .special_forms import special_form_module_name_name_tuple_to_type_annotation, \
    special_form_typeshed_class_to_typeshed_class_definition
from .type_definitions import *


EMPTY_CLASS_DEFINITION = TypeshedClassDefinition(
    type_variable_list=list(),
    method_name_to_method_list_dict=dict(),
    class_variable_name_to_type_annotation_dict=dict()
)

class Client:
    __slots__ = (
        'search_context',
        'module_name_to_module_stub_names_dict_or_none',
        'module_name_name_tuple_to_lookup_result_dict',
        'module_name_name_tuple_to_recursive_union_type_variable_dict',
        'concrete_class_to_class_definition_dict',
        'function_to_function_definition_dict',
        'known_class_inheritance_graph'
    )

    def __init__(self):
        filename: str = getframeinfo(currentframe()).filename
        parent: Path = Path(filename).resolve().parent
        typeshed: Path = parent / 'stdlib'

        # NO querying non-bundled typeshed stubs
        self.search_context: SearchContext = get_search_context(typeshed=typeshed, search_path=[])

        # Cache queried type stub names dicts for modules
        self.module_name_to_module_stub_names_dict_or_none: dict[
            str,
            Optional[dict[str, typeshed_client.NameInfo]]
        ] = dict()

        # Cache name lookups
        self.module_name_name_tuple_to_lookup_result_dict: dict[
            tuple[str, str],
            TypeshedTypeAnnotation
        ] = dict()

        # Cache queried class definitions
        self.concrete_class_to_class_definition_dict: dict[TypeshedClass, TypeshedClassDefinition] = {
            special_form_typeshed_class: typeshed_class_definition
            for special_form_typeshed_class, typeshed_class_definition
            in special_form_typeshed_class_to_typeshed_class_definition.items()
        }

        # Cache queried function definitions
        self.function_to_function_definition_dict = dict()

        # Used for creating RecusiveoUnions
        self.module_name_name_tuple_to_recursive_union_type_variable_dict: dict[
            tuple[str, str],
            TypeshedTypeVariable
        ] = dict()

        self.known_class_inheritance_graph = nx.DiGraph()

    def get_module_stub_names_dict_or_none(self, module_name: str) -> Optional[dict[str, typeshed_client.NameInfo]]:
        if module_name not in self.module_name_to_module_stub_names_dict_or_none:
            self.module_name_to_module_stub_names_dict_or_none[module_name] = typeshed_client.parser.get_stub_names(
                module_name,
                search_context=self.search_context
            )

        return self.module_name_to_module_stub_names_dict_or_none[module_name]

    # Look up name
    # Raises ModuleNotFoundError, AttributeError
    def look_up_name(self, module_name: str, name: str) -> TypeshedNameLookupResult:
        if module_name is None or name is None:
            import pudb
            pudb.set_trace()

        # Use cache if possible
        if (module_name, name) in self.module_name_name_tuple_to_lookup_result_dict:
            return self.module_name_name_tuple_to_lookup_result_dict[(module_name, name)]

        # Special path for handling RecusiveUnions
        # DO NOT CACHE this result
        elif (module_name, name) in self.module_name_name_tuple_to_recursive_union_type_variable_dict:
            return self.module_name_name_tuple_to_recursive_union_type_variable_dict[
                (module_name, name)
            ]

        else:
            # Special path for handling nested modules
            if self.get_module_stub_names_dict_or_none(module_name + '.' + name) is not None:
                return_value = TypeshedModule(module_name + '.' + name)

            else:
                # Used for handling mismatches between runtime class names and Typeshed class names.
                if (module_name, name) in runtime_class_name_tuple_to_typeshed_class_name_tuple:
                    module_name, name = runtime_class_name_tuple_to_typeshed_class_name_tuple[(module_name, name)]
                
                # Used for treating `typing._SpecialForm`'s as classes to allow them to be subscribed.
                if (module_name, name) in special_form_module_name_name_tuple_to_type_annotation:
                    return_value = special_form_module_name_name_tuple_to_type_annotation[(module_name, name)]

                # Fallback case: retrieve and parse stubs.
                else:
                    module_stub_names_dict = self.get_module_stub_names_dict_or_none(module_name)

                    if module_stub_names_dict is None:
                        raise ModuleNotFoundError(f"No module named '{module_name}'")

                    if name not in module_stub_names_dict:
                        # Look up name in builtins as a backup plan
                        builtins_module_stub_names_dict = self.get_module_stub_names_dict_or_none('builtins')
                        assert builtins_module_stub_names_dict is not None

                        if name in builtins_module_stub_names_dict:
                            return_value = self.look_up_name('builtins', name)
                        else:
                            raise AttributeError(f"module '{module_name}' has no attribute '{name}'")
                    else:

                        name_info = module_stub_names_dict[name]
                        name_info_ast = name_info.ast

                        # ast.ClassDef
                        if isinstance(name_info_ast, ast.ClassDef):
                            return_value = TypeshedClass(module_name, name_info_ast.name)
                        # ast.FunctionDef, ast.AsyncFunctionDef
                        elif isinstance(name_info_ast, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            return_value = TypeshedFunction(module_name, name_info_ast.name)
                        # typeshed_client.parser.OverloadedName
                        elif isinstance(name_info_ast, typeshed_client.parser.OverloadedName):
                            function_name = None

                            for definition in name_info_ast.definitions:
                                assert isinstance(definition, (ast.FunctionDef, ast.AsyncFunctionDef))
                                function_name = definition.name

                            assert isinstance(function_name, str)
                            return_value = TypeshedFunction(module_name, function_name)
                        # typeshed_client.ImportedName
                        elif isinstance(name_info_ast, typeshed_client.ImportedName):
                            new_module_name = '.'.join(name_info_ast.module_name)
                            new_name = name_info_ast.name

                            assert self.get_module_stub_names_dict_or_none(new_module_name) is not None

                            # new_name is None, should be a module
                            if new_name is None:
                                return_value = TypeshedModule(new_module_name)
                            # new_name is not None, something else
                            else:
                                assert isinstance(new_name, str)
                                return_value = self.look_up_name(new_module_name, new_name)
                        # ast.Assign
                        # _T = TypeVar("_T")
                        # AnyStr = TypeVar("AnyStr", str, bytes)
                        # _T_co = TypeVar("_T_co", covariant=True)
                        # _OpenFile = StrOrBytesPath | int
                        # _LiteralInteger = _PositiveInteger | _NegativeInteger | Literal[0]
                        # EnvironmentError = OSError
                        # UserId = NewType('UserId', int)
                        # open = builtins.open
                        elif isinstance(name_info_ast, ast.Assign):
                            # Parse the RHS
                            return_value = self.parse_ast_expr_to_lookup_result(module_name, name_info_ast.value)
                        # ast.AnnAssign
                        # _PositiveInteger: TypeAlias = Literal[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
                        # ReadOnlyBuffer: TypeAlias = bytes  # stable
                        # WriteableBuffer: TypeAlias = bytearray | memoryview | array.array[Any] | mmap.mmap | ctypes._CData
                        # _ClassInfo: TypeAlias = type | types.UnionType | tuple[_ClassInfo, ...]
                        # NotImplemented: _NotImplementedType
                        # Ellipsis: ellipsis
                        # _inst: Random = ...
                        elif isinstance(name_info_ast, ast.AnnAssign):
                            name_info_ast_target = name_info_ast.target
                            name_info_ast_annotation = name_info_ast.annotation
                            name_info_ast_value = name_info_ast.value

                            assert isinstance(name_info_ast_target, ast.Name)

                            # Parse the annotation
                            parsed_name_info_ast_annotation = self.parse_ast_expr_to_type_annotation(
                                module_name,
                                name_info_ast_annotation
                            )

                            # Idiom 1: annotation is TypeAlias
                            # Parse the RHS
                            if parsed_name_info_ast_annotation in (
                                    TypeshedClass('typing', 'TypeAlias'),
                                    TypeshedClass('typing_extensions', 'TypeAlias'),
                            ):
                                assert name_info_ast_value is not None

                                # Initialize a TypeVariable representing a possible RecursiveUnion
                                if (
                                        module_name,
                                        name_info_ast_target.id
                                ) not in self.module_name_name_tuple_to_recursive_union_type_variable_dict:
                                    self.module_name_name_tuple_to_recursive_union_type_variable_dict[
                                        (module_name, name_info_ast_target.id)
                                    ] = TypeshedTypeVariable()

                                recursive_union_type_variable = \
                                    self.module_name_name_tuple_to_recursive_union_type_variable_dict[
                                        (module_name, name_info_ast_target.id)
                                    ]

                                parsed_name_info_ast_value = self.parse_ast_expr_to_type_annotation(
                                    module_name,
                                    name_info_ast_value
                                )

                                if isinstance(parsed_name_info_ast_value, (TypeshedClass, Subscription)):
                                    return_value = parsed_name_info_ast_value
                                elif isinstance(parsed_name_info_ast_value, Union):
                                    # Create RecursiveUnion if necessary.
                                    if recursive_union_type_variable in iterate_type_variables_in_type_annotation(
                                            parsed_name_info_ast_value
                                    ):
                                        return_value = RecursiveUnion(
                                            recursive_union_type_variable,
                                            parsed_name_info_ast_value.type_annotation_frozenset
                                        )
                                    else:
                                        return_value = parsed_name_info_ast_value
                                else:
                                    assert False, f"Cannot handle TypeAlias with value {ast.unparse(name_info_ast_value)}"
                            # Idiom 2: TypeshedClass
                            else:
                                assert isinstance(parsed_name_info_ast_annotation, TypeshedClass)
                                return_value = parsed_name_info_ast_annotation
                        else:
                            assert False, f"Cannot handle node {ast.unparse(name_info_ast)} in module {module_name}"

            # Save return_value to cache and return
            self.module_name_name_tuple_to_lookup_result_dict[(module_name, name)] = return_value
            return return_value

    # Raises ModuleNotFoundError, AttributeError 
    def getattr_on_lookup_result(
            self,
            lookup_result: TypeshedNameLookupResult,
            components: list[str]
    ) -> TypeshedNameLookupResult:
        # No more components remaining
        if len(components) == 0:
            return lookup_result

        # Otherwise,
        # Parse the first component
        # And recurse on the remaining components
        else:
            first_component = components[0]
            remaining_components = components[1:]

            if isinstance(lookup_result, TypeshedModule):
                first_component_lookup_result = self.look_up_name(
                    lookup_result.module_name,
                    first_component
                )

            elif isinstance(lookup_result, TypeshedClass):
                if lookup_result != TypeshedClass('typing', 'Any'):
                    class_definition = self.get_class_definition(
                        lookup_result
                    )

                    if first_component in class_definition.method_name_to_method_list_dict:
                        first_component_lookup_result = TypeshedMethod(
                            lookup_result.module_name,
                            lookup_result.class_name,
                            first_component
                        )
                    elif first_component in class_definition.class_variable_name_to_type_annotation_dict:
                        return class_definition.class_variable_name_to_type_annotation_dict[
                            first_component
                        ]
                    else:
                        raise AttributeError(f"{lookup_result} has no attribute '{first_component}'")
                # Any attribute access is possible on typing.Any
                else:
                    return TypeshedClass('typing', 'Any')
            # Type variables are treated as typing.Any
            elif isinstance(lookup_result, TypeshedTypeVariable):
                return TypeshedClass('typing', 'Any') 
            else:
                assert False, f"Cannot getattr '{first_component}' on {lookup_result}"

            return self.getattr_on_lookup_result(
                first_component_lookup_result,
                remaining_components
            )

    def recursively_parse_ast_tuple_ast_list(
        self,
        module_name: str,
        node: tUnion[ast.Tuple, ast.List]
    ) -> Generator[TypeshedTypeAnnotation, None, None]:
        for elt in node.elts:
            if isinstance(elt, tUnion[ast.Tuple, ast.List]):
                yield from self.recursively_parse_ast_tuple_ast_list(module_name, elt)
            else:
                yield self.parse_ast_expr_to_type_annotation(module_name, elt)

    def parse_ast_expr_to_type_annotation(
            self,
            module_name: str,
            node: Optional[ast.expr]
    ) -> TypeshedTypeAnnotation:
        lookup_result = self.parse_ast_expr_to_lookup_result(module_name, node)
        assert isinstance(lookup_result, TypeshedTypeAnnotation)
        return simplify_type_annotation(lookup_result)

    def parse_ast_expr_to_lookup_result(
            self,
            module_name: str,
            node: Optional[ast.expr] 
    ) -> TypeshedNameLookupResult:
        # Name(id='object')
        # Name(id='_KT')
        if isinstance(node, ast.Name):
            return self.look_up_name(module_name, node.id)

        # Attribute(value=Name(id='types'), attr='UnionType')
        elif isinstance(node, ast.Attribute):
            components: list[str] = list(iterate_components_in_ast_attribute(node))

            getattr_result = self.getattr_on_lookup_result(
                TypeshedModule(module_name),
                components
            )

            return getattr_result

        # Subscript(value=Name(id='Protocol'), slice=Index(value=Name(id='_T_co')))
        # Subscript(value=Name(id='_FutureLike'), slice=Name(id='_T'))
        elif isinstance(node, ast.Subscript):
            # Parse node.value to get parsed_node_value
            assert isinstance(
                node.value,
                (ast.Name, ast.Attribute)
            ), f"Cannot parse {ast.unparse(node.value)} in ast.Subscript {ast.unparse(node)}"

            parsed_node_value: TypeshedTypeAnnotation = self.parse_ast_expr_to_type_annotation(module_name, node.value)

            # Parse node.slice to get parsed_node_slice
            assert isinstance(
                node.slice,
                (
                    ast.Name,
                    ast.Attribute,
                    ast.Subscript,
                    ast.BinOp,
                    ast.Tuple,
                    ast.Constant,
                    ast.UnaryOp
                )
            ), f"Cannot parse {ast.unparse(node.slice)} in ast.Subscript {ast.unparse(node)}"

            if isinstance(node.slice, ast.Tuple):
                type_annotation_list: list[TypeshedTypeAnnotation] = list(self.recursively_parse_ast_tuple_ast_list(module_name, node.slice))
            else:
                parsed_node_slice = self.parse_ast_expr_to_type_annotation(module_name, node.slice)
                type_annotation_list: list[TypeshedTypeAnnotation] = [parsed_node_slice]

            return simplify_type_annotation(
                subscribe(parsed_node_value, tuple(type_annotation_list))
            )

        # BinOp(left=BinOp(left=BinOp(left=BinOp(left=Name(id='str'), op=BitOr(), right=Name(id='ReadableBuffer'))
        elif isinstance(node, ast.BinOp):
            assert isinstance(node.op, ast.BitOr)

            list_instance = list()

            # recursively parse node.left
            parsed_node_left = self.parse_ast_expr_to_type_annotation(module_name, node.left)

            # update list_instance
            if isinstance(parsed_node_left, Union):
                list_instance.extend(parsed_node_left.type_annotation_frozenset)
            else:
                list_instance.append(parsed_node_left)

            parsed_node_right = self.parse_ast_expr_to_type_annotation(module_name, node.right)

            # update list_instance
            if isinstance(parsed_node_right, Union):
                list_instance.extend(parsed_node_right.type_annotation_frozenset)
            else:
                list_instance.append(parsed_node_right)

            return simplify_type_annotation(Union(frozenset(list_instance)))

        # Constant(value=Ellipsis)
        elif isinstance(node, ast.Constant):
            node_value_type = type(node.value)
            return from_runtime_class(node_value_type)

        # UnaryOp(op=USub(), operand=Constant(value=1, kind=None))
        elif isinstance(node, ast.UnaryOp):
            evaluation_result = ast.literal_eval(node)
            evaluation_result_type = type(evaluation_result)
            return from_runtime_class(evaluation_result_type)

        # TypeVar("_T")
        # TypeVar("AnyStr", str, bytes)
        # TypeVar("_T_co", covariant=True)
        # NewType('UserId', int)
        elif isinstance(node, ast.Call):
            name_info_ast_value_func_type_annotation = self.parse_ast_expr_to_lookup_result(
                module_name,
                node.func
            )

            if name_info_ast_value_func_type_annotation in (
                    TypeshedClass('typing', 'TypeVar'),
                    TypeshedClass('typing', 'ParamSpec'),
                    TypeshedClass('typing_extensions', 'ParamSpec'),
            ):
                # TypeVar(name, *constraints, bound=None, covariant=False, contravariant=False)
                # AnyStr = TypeVar("AnyStr", str, bytes)
                # _P = ParamSpec("_P")
                name_arg = node.args[0]
                assert isinstance(name_arg, ast.Constant) and isinstance(name_arg.value, str)

                # Create a corresponding TypeVariable if not already created
                typevar_name = name_arg.value

                if (module_name, typevar_name) not in self.module_name_name_tuple_to_recursive_union_type_variable_dict:
                    self.module_name_name_tuple_to_recursive_union_type_variable_dict[
                        (module_name, typevar_name)
                    ] = TypeshedTypeVariable()

                constraints = node.args[1:]
                if not constraints:
                    # If there are no constraints, simply return the corresponding TypeVariable
                    return self.module_name_name_tuple_to_recursive_union_type_variable_dict[
                        (module_name, typevar_name)
                    ]
                else:
                    # If there are constraints, return them as a Union
                    parsed_constraints_list = []
                    for constraint in constraints:
                        parsed_constraint = self.parse_ast_expr_to_type_annotation(
                            module_name,
                            constraint
                        )
                        parsed_constraints_list.append(parsed_constraint)

                    return simplify_type_annotation(Union(frozenset(parsed_constraints_list)))
            elif name_info_ast_value_func_type_annotation == TypeshedClass('typing', 'NewType'):
                second_arg = node.args[1]
                assert isinstance(second_arg, ast.Name)
                return self.look_up_name(module_name, second_arg.id)
            else:
                assert False, f"Cannot parse call {ast.unparse(node)} in module {module_name}"
        # ("lineno", "tag") in __match_args__ = ("lineno", "tag")
        elif isinstance(node, ast.Tuple):
            return from_runtime_class(tuple)
        elif node is None:
            return TypeshedClass('typing', 'Any')

        else:
            import pudb; pudb.set_trace()
            assert False, f"Cannot handle node {ast.unparse(node)} in module {module_name}"

    def parse_ast_class_def_to_definition(
            self,
            class_: TypeshedClass,
            class_def: ast.ClassDef,
            child_nodes: dict
    ) -> TypeshedClassDefinition:
        self.known_class_inheritance_graph.add_node(class_)

        class_level_type_variable_ordered_set = OrderedSet()

        method_name_to_method_list_dict = dict()

        class_variable_name_to_type_annotation_dict = dict()

        if class_def.bases:
            all_type_variables_in_base_class_type_annotations: OrderedSet[TypeshedTypeVariable] = OrderedSet()
            typing_generic_in_base_classes: bool = False
            type_variables_in_typing_generic_type_annotations: OrderedSet[TypeshedTypeVariable] = OrderedSet()

            for base in class_def.bases:
                # Parse AST node to type annotation
                # Should be ConcreteClass or Subscription
                base_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name, base)

                if isinstance(base_type_annotation, TypeshedClass):
                    base_class = base_type_annotation
                    base_class_type_annotation_list = []
                elif isinstance(base_type_annotation, Subscription):
                    base_class = base_type_annotation.subscribed_class
                    base_class_type_annotation_list = list(base_type_annotation.type_annotation_tuple)
                else:
                    assert False, f"Cannot handle base type {base_type_annotation} in {class_}"

                for base_class_type_annotation in base_class_type_annotation_list:
                    if isinstance(base_class_type_annotation, TypeshedTypeVariable):
                        all_type_variables_in_base_class_type_annotations.add(base_class_type_annotation)

                self.known_class_inheritance_graph.add_edge(class_, base_class)

                if base_class == TypeshedClass('typing', 'Generic'):
                    typing_generic_in_base_classes = True
                    for base_class_type_annotation in base_class_type_annotation_list:
                        if isinstance(base_class_type_annotation, TypeshedTypeVariable):
                            type_variables_in_typing_generic_type_annotations.add(base_class_type_annotation)

                # Eagerly resolve base class
                base_class_definition = self.get_class_definition_without_resolving_typing_self(base_class)

                base_class_definition_with_instantiated_type_variables = instantiate_type_variables_in_class_definition(
                    base_class_definition,
                    base_class_type_annotation_list
                )

                method_name_to_method_list_dict.update(
                    base_class_definition_with_instantiated_type_variables.method_name_to_method_list_dict
                )

                class_variable_name_to_type_annotation_dict.update(
                    base_class_definition_with_instantiated_type_variables.class_variable_name_to_type_annotation_dict
                )

            # https://mypy.readthedocs.io/en/stable/generics.html
            # The order of type variables is defined by the following rules:
            # If Generic[...] is present, then the order of variables is always determined by their order in Generic[...].
            # If there are no Generic[...] in bases, then all type variables are collected in the lexicographic order (i.e. by first appearance).
            if typing_generic_in_base_classes:
                class_level_type_variable_ordered_set = type_variables_in_typing_generic_type_annotations
            else:
                class_level_type_variable_ordered_set = all_type_variables_in_base_class_type_annotations
        else:
            if class_ != TypeshedClass('builtins', 'object'):
                base_class = TypeshedClass('builtins', 'object')

                self.known_class_inheritance_graph.add_edge(class_, base_class)

                base_class_type_annotation_list = []

                # Eagerly resolve base class
                base_class_definition = self.get_class_definition_without_resolving_typing_self(base_class)

                base_class_definition_with_instantiated_type_variables = instantiate_type_variables_in_class_definition(
                    base_class_definition,
                    base_class_type_annotation_list
                )

                method_name_to_method_list_dict.update(
                    base_class_definition_with_instantiated_type_variables.method_name_to_method_list_dict
                )

                class_variable_name_to_type_annotation_dict.update(
                    base_class_definition_with_instantiated_type_variables.class_variable_name_to_type_annotation_dict
                )

        class_level_type_variable_list = list(class_level_type_variable_ordered_set)

        # Add methods and properties
        for child_node_name, child_node in child_nodes.items():
            child_node_ast = child_node.ast

            if isinstance(child_node_ast, (ast.FunctionDef, ast.AsyncFunctionDef)):
                method_name_to_method_list_dict[child_node_name] = [
                    self.parse_method_ast_function_def_to_definition(
                        class_,
                        child_node_ast,
                        class_level_type_variable_ordered_set
                    )
                ]

            # Method
            elif isinstance(child_node_ast, typeshed_client.parser.OverloadedName):
                method_name_to_method_list_dict[child_node_name] = []
                for definition in child_node_ast.definitions:
                    assert isinstance(definition, (ast.FunctionDef, ast.AsyncFunctionDef))

                    method_name_to_method_list_dict[child_node_name].append(self.parse_method_ast_function_def_to_definition(
                        class_,
                        definition,
                        class_level_type_variable_ordered_set
                    ))

            # Property
            elif isinstance(child_node_ast, ast.AnnAssign):
                parsed_annotation = self.parse_ast_expr_to_type_annotation(
                    class_.module_name,
                    child_node_ast.annotation
                )
                assert isinstance(parsed_annotation, TypeshedTypeAnnotation)
                class_variable_name_to_type_annotation_dict[child_node_name] = parsed_annotation

            # Method or property
            elif isinstance(child_node_ast, ast.Assign):
                # __ror__ = __or__
                if isinstance(child_node_ast.value, ast.Name):
                    child_node_ast_value_id: str = child_node_ast.value.id

                    # Previously defined method name
                    if child_node_ast_value_id in method_name_to_method_list_dict:
                        method_name_to_method_list_dict[child_node_name] = \
                            method_name_to_method_list_dict[child_node_ast_value_id]

                    # Previously defined class variable name
                    elif child_node_ast_value_id in class_variable_name_to_type_annotation_dict:
                        class_variable_name_to_type_annotation_dict[child_node_name] = \
                            class_variable_name_to_type_annotation_dict[child_node_ast_value_id]

                    # Resolve name in global scope
                    else:
                        class_variable_name_to_type_annotation_dict[child_node_name] = \
                            self.look_up_name(class_.module_name, child_node_ast_value_id)
                else:
                    # Parse assigned ast.expr in global scope
                    lookup_result = self.parse_ast_expr_to_lookup_result(class_.module_name, child_node_ast.value)
                    if isinstance(lookup_result, TypeshedTypeAnnotation):
                        type_annotation = simplify_type_annotation(lookup_result)
                        class_variable_name_to_type_annotation_dict[child_node_name] = type_annotation
                    # propagate = Misc.pack_propagate (in tkinter.Pack)
                    elif isinstance(lookup_result, TypeshedMethod):
                        typeshed_class = TypeshedClass(lookup_result.module_name, lookup_result.class_name)
                        class_definition = self.get_class_definition_without_resolving_typing_self(typeshed_class)
                        method_name_to_method_list_dict[child_node_name] = class_definition.method_name_to_method_list_dict[lookup_result.function_name]
            # Others (such as nested classes)
            else:
                logging.error("Cannot resolve node %s in class %s. Treating it as a class variable of type typing.Any", ast.unparse(child_node_ast), class_)
                class_variable_name_to_type_annotation_dict[child_node_name] = TypeshedClass('typing', 'Any')

        return TypeshedClassDefinition(
            class_level_type_variable_list,
            method_name_to_method_list_dict,
            class_variable_name_to_type_annotation_dict
        )

    def parse_method_ast_function_def_to_definition(
            self,
            class_: TypeshedClass,
            function_def: tUnion[ast.FunctionDef, ast.AsyncFunctionDef],
            class_level_type_variable_set
    ) -> TypeshedFunctionDefinition:
        # copy the original class_level_type_variable_set
        class_level_type_variable_set_copy = class_level_type_variable_set.copy()

        parameter_type_annotation_list = list()

        args = function_def.args

        args_posonlyargs = args.posonlyargs
        assert not args_posonlyargs

        args_args = args.args

        for i, arg in enumerate(args_args):
            # arg(
            # arg='__iterable',
            # annotation=Subscript(value=Name(id='SupportsIter'), slice=Index(value=Name(id='_SupportsNextT'))),
            # type_comment=None
            # )
            # arg(arg='__o', annotation=Name(id='object'), type_comment=None)
            if arg.annotation is not None:
                try:
                    arg_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name, arg.annotation)
                except (ModuleNotFoundError, AttributeError):
                    logging.error("Failed to parse annotation %s in class %s. Using typing.Any", ast.unparse(arg.annotation), class_)
                    arg_type_annotation = TypeshedClass('typing', 'Any')
            else:
                arg_type_annotation = TypeshedClass('typing', 'Any')

            class_level_type_variable_set_copy.update(iterate_type_variables_in_type_annotation(arg_type_annotation))

            parameter_type_annotation_list.append(arg_type_annotation)

        args_vararg = args.vararg
        if args_vararg:
            vararg_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name, args_vararg.annotation)
            class_level_type_variable_set_copy.update(iterate_type_variables_in_type_annotation(vararg_type_annotation))
        else:
            vararg_type_annotation = None

        kwonlyargs_name_to_type_annotation_dict = dict()

        args_kwonlyargs = args.kwonlyargs
        for kwonlyarg in args_kwonlyargs:
            kwonlyarg_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name, kwonlyarg.annotation)

            kwonlyargs_name_to_type_annotation_dict[kwonlyarg.arg] = kwonlyarg_type_annotation

            class_level_type_variable_set_copy.update(
                iterate_type_variables_in_type_annotation(kwonlyarg_type_annotation))

        args_kwarg = args.kwarg
        if args_kwarg:
            kwarg_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name, args_kwarg.annotation)

            class_level_type_variable_set_copy.update(iterate_type_variables_in_type_annotation(kwarg_type_annotation))
        else:
            kwarg_type_annotation = None

        return_value_type_annotation = self.parse_ast_expr_to_type_annotation(class_.module_name,
                                                                            function_def.returns)

        class_level_type_variable_set_copy.update(
            iterate_type_variables_in_type_annotation(return_value_type_annotation))

        method_level_type_variable_set = class_level_type_variable_set_copy - class_level_type_variable_set

        return TypeshedFunctionDefinition(
            list(method_level_type_variable_set),
            parameter_type_annotation_list,
            vararg_type_annotation,
            kwonlyargs_name_to_type_annotation_dict,
            kwarg_type_annotation,
            return_value_type_annotation
        )

    def parse_global_function_or_staticmethod_ast_function_def_to_definition(
            self,
            global_function_or_concrete_class: tUnion[TypeshedFunction, TypeshedClass],
            function_def: tUnion[ast.FunctionDef, ast.AsyncFunctionDef]
    ) -> TypeshedFunctionDefinition:
        global_function_level_type_variable_ordered_set = OrderedSet()

        parameter_type_annotation_list = list()

        args = function_def.args

        args_posonlyargs = args.posonlyargs
        assert not args_posonlyargs

        args_args = args.args

        for i, arg in enumerate(args_args):
            # arg(
            # arg='__iterable',
            # annotation=Subscript(value=Name(id='SupportsIter'), slice=Index(value=Name(id='_SupportsNextT'))),
            # type_comment=None
            # )
            # arg(arg='__o', annotation=Name(id='object'), type_comment=None)
            arg_type_annotation = self.parse_ast_expr_to_type_annotation(
                global_function_or_concrete_class.module_name,
                arg.annotation
            )

            for type_variable in iterate_type_variables_in_type_annotation(arg_type_annotation):
                global_function_level_type_variable_ordered_set.add(type_variable)

            parameter_type_annotation_list.append(arg_type_annotation)

        args_vararg = args.vararg
        if args_vararg:
            vararg_type_annotation = self.parse_ast_expr_to_type_annotation(
                global_function_or_concrete_class.module_name,
                args_vararg.annotation
            )

            for type_variable in iterate_type_variables_in_type_annotation(vararg_type_annotation):
                global_function_level_type_variable_ordered_set.add(type_variable)
        else:
            vararg_type_annotation = None

        kwonlyargs_name_to_type_annotation_dict = dict()

        args_kwonlyargs = args.kwonlyargs
        for kwonlyarg in args_kwonlyargs:
            kwonlyarg_type_annotation = self.parse_ast_expr_to_type_annotation(
                global_function_or_concrete_class.module_name,
                kwonlyarg.annotation
            )

            kwonlyargs_name_to_type_annotation_dict[kwonlyarg.arg] = kwonlyarg_type_annotation

            for type_variable in iterate_type_variables_in_type_annotation(kwonlyarg_type_annotation):
                global_function_level_type_variable_ordered_set.add(type_variable)

        args_kwarg = args.kwarg
        if args_kwarg:
            kwarg_type_annotation = self.parse_ast_expr_to_type_annotation(
                global_function_or_concrete_class.module_name,
                args_kwarg.annotation
            )

            for type_variable in iterate_type_variables_in_type_annotation(kwarg_type_annotation):
                global_function_level_type_variable_ordered_set.add(type_variable)
        else:
            kwarg_type_annotation = None

        return_value_type_annotation = self.parse_ast_expr_to_type_annotation(
            global_function_or_concrete_class.module_name,
            function_def.returns
        )

        for type_variable in iterate_type_variables_in_type_annotation(return_value_type_annotation):
            global_function_level_type_variable_ordered_set.add(type_variable)

        return TypeshedFunctionDefinition(
            list(global_function_level_type_variable_ordered_set),
            parameter_type_annotation_list,
            vararg_type_annotation,
            kwonlyargs_name_to_type_annotation_dict,
            kwarg_type_annotation,
            return_value_type_annotation
        )

    # Raises ModuleNotFoundError
    def get_all_class_definitions_in_module(self, module_name: str) -> dict[TypeshedClass, TypeshedClassDefinition]:
        all_classes_in_module: dict[TypeshedClass, TypeshedClassDefinition] = dict()

        module_stub_names_dict = self.get_module_stub_names_dict_or_none(module_name)

        if module_stub_names_dict is None:
            raise ModuleNotFoundError(f"No module named '{module_name}'")

        for name, name_info in module_stub_names_dict.items():
            if isinstance(name_info.ast, ast.ClassDef):
                concrete_class: TypeshedClass = TypeshedClass(module_name, name_info.ast.name)
                if concrete_class not in self.concrete_class_to_class_definition_dict:
                    self.concrete_class_to_class_definition_dict[concrete_class] = \
                        self.parse_ast_class_def_to_definition(concrete_class, name_info.ast, name_info.child_nodes)

                all_classes_in_module[concrete_class] = self.concrete_class_to_class_definition_dict[concrete_class]

        return all_classes_in_module

    # Raises ModuleNotFoundError, AttributeError
    def get_class_definition(self, concrete_class: TypeshedClass) -> TypeshedClassDefinition:
        class_definition_without_resolving_typing_self = self.get_class_definition_without_resolving_typing_self(
            concrete_class
        )

        type_annotation_of_self = get_type_annotation_of_self(
            concrete_class,
            class_definition_without_resolving_typing_self.type_variable_list
        )

        return replace_typing_self_in_class_definition(
            class_definition_without_resolving_typing_self,
            type_annotation_of_self
        )

    # Raises ModuleNotFoundError, AttributeError
    def get_class_definition_without_resolving_typing_self(self, concrete_class: TypeshedClass) -> TypeshedClassDefinition:
        if concrete_class in self.concrete_class_to_class_definition_dict:
            class_definition = self.concrete_class_to_class_definition_dict[concrete_class]
            if class_definition == EMPTY_CLASS_DEFINITION:
                logging.error("Attempting to get the definition of %s within the class itself. Returning empty class definition.", concrete_class)
            return class_definition
        else:
            # Insert empty class definition to prevent repetitive recursive calls
            self.concrete_class_to_class_definition_dict[concrete_class] = EMPTY_CLASS_DEFINITION
            module_stub_names_dict = self.get_module_stub_names_dict_or_none(
                concrete_class.module_name
            )

            if module_stub_names_dict is None:
                raise ModuleNotFoundError(f"No module named '{concrete_class.module_name}'")

            if concrete_class.class_name not in module_stub_names_dict:
                raise AttributeError(
                    f"module '{concrete_class.module_name}' has no attribute '{concrete_class.class_name}'")

            name_info = module_stub_names_dict[concrete_class.class_name]

            if isinstance(name_info.ast, ast.ClassDef):
                return_value = self.parse_ast_class_def_to_definition(concrete_class, name_info.ast, name_info.child_nodes)
            else:
                logging.error("%s is not actually a class. Returning empty class definition.", concrete_class)
                return_value = EMPTY_CLASS_DEFINITION

            self.concrete_class_to_class_definition_dict[concrete_class] = return_value
            return return_value

    # Raises ModuleNotFoundError, AttributeError
    def get_function_definition(self, function: TypeshedFunction) -> list[TypeshedFunctionDefinition]:
        if function in self.function_to_function_definition_dict:
            return self.function_to_function_definition_dict[function]
        else:
            module_stub_names_dict = self.get_module_stub_names_dict_or_none(
                function.module_name
            )

            if module_stub_names_dict is None:
                raise ModuleNotFoundError(f"No module named '{function.module_name}'")

            if function.function_name not in module_stub_names_dict:
                raise AttributeError(f"module '{function.module_name}' has no attribute '{function.function_name}'")

            name_info = module_stub_names_dict[function.function_name]

            if isinstance(name_info.ast, (ast.FunctionDef, ast.AsyncFunctionDef)):
                return_value = [self.parse_global_function_or_staticmethod_ast_function_def_to_definition(function, name_info.ast)]

            elif isinstance(name_info.ast, typeshed_client.parser.OverloadedName):
                return_value = []
                for definition in name_info.ast.definitions:
                    assert isinstance(definition, (ast.FunctionDef, ast.AsyncFunctionDef))

                    return_value.append(self.parse_global_function_or_staticmethod_ast_function_def_to_definition(function, definition))

            else:
                assert False, f"Cannot handle {function}"

            self.function_to_function_definition_dict[function] = return_value
            return return_value
