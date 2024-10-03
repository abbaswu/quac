import collections.abc
import importlib
import logging
import typing
from collections import defaultdict
from typing import Generator, Optional, Union

from ordered_set import OrderedSet

from typeshed_client_ex.runtime_class_name_tuples_and_typeshed_class_name_tuples import \
    runtime_class_name_tuple_to_typeshed_class_name_tuple, typeshed_class_name_tuple_to_runtime_class


# Typeshed Type Annotation

class TypeshedTypeVariable:
    pass


class TypeshedClass:
    __slots__ = ('module_name', 'class_name')

    def __init__(
            self,
            module_name: str,
            class_name: str,
    ):
        self.module_name: str = module_name
        self.class_name: str = class_name

    def __eq__(self, other: object) -> bool:
        if isinstance(other,
                      TypeshedClass) and self.module_name == other.module_name and self.class_name == other.class_name:
            return True
        else:
            return False

    def __hash__(self) -> int:
        return hash((self.module_name, self.class_name))

    def __repr__(self) -> str:
        # Special handling for the type of None and Ellipsis
        if self == from_runtime_class(type(None)):
            return 'None'
        elif self == from_runtime_class(type(Ellipsis)):
            return '...'
        else:
            return f'{self.module_name}.{self.class_name}'


def to_runtime_class(typeshed_class: TypeshedClass) -> Optional[type]:
    typeshed_class_module = typeshed_class.module_name
    typeshed_class_name = typeshed_class.class_name

    typeshed_class_name_tuple = (typeshed_class_module, typeshed_class_name)
    if typeshed_class_name_tuple in typeshed_class_name_tuple_to_runtime_class:
        runtime_class = typeshed_class_name_tuple_to_runtime_class[typeshed_class_name_tuple]
        return runtime_class
    else:
        runtime_class_module = typeshed_class_module
        runtime_class_name = typeshed_class_name

        try:
            module = importlib.import_module(runtime_class_module)
            runtime_class = module.__dict__[runtime_class_name]
            assert isinstance(runtime_class, type)
            return runtime_class
        except (ModuleNotFoundError, KeyError, AssertionError):
            logging.error(f'Failed to convert %s into a runtime class.', typeshed_class)
            return None


def from_runtime_class(
        runtime_class: type
) -> TypeshedClass:
    runtime_class_module = runtime_class.__module__
    runtime_class_name = runtime_class.__name__

    runtime_class_name_tuple = (runtime_class_module, runtime_class_name)
    if runtime_class_name_tuple in runtime_class_name_tuple_to_typeshed_class_name_tuple:
        typeshed_class_module, typeshed_class_name = runtime_class_name_tuple_to_typeshed_class_name_tuple[runtime_class_name_tuple]
        return TypeshedClass(typeshed_class_module, typeshed_class_name)
    else:
        return TypeshedClass(runtime_class_module, runtime_class_name)


class Subscription:
    __slots__ = ('subscribed_class', 'type_annotation_tuple')

    def __init__(self, subscribed_class: TypeshedClass, type_annotation_tuple: tuple['TypeshedTypeAnnotation', ...]):
        self.subscribed_class = subscribed_class
        self.type_annotation_tuple = type_annotation_tuple

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Subscription):
            return (
                    self.subscribed_class == other.subscribed_class
                    and self.type_annotation_tuple == other.type_annotation_tuple
            )
        return False

    def __hash__(self) -> int:
        return hash((self.subscribed_class, self.type_annotation_tuple))

    def __repr__(self) -> str:
        subscribed_class_string: str = str(self.subscribed_class)

        # Special handling for typing.Callable
        # https://docs.python.org/3/library/typing.html#annotating-callable-objects
        if subscribed_class_string == 'typing.Callable' and self.type_annotation_tuple:
            parameter_type_annotations = self.type_annotation_tuple[:-1]
            return_value_type_annotation = self.type_annotation_tuple[-1]

            if (
                    len(parameter_type_annotations) == 1
                    and parameter_type_annotations[0] == from_runtime_class(type(Ellipsis))
            ):
                return ''.join((
                    subscribed_class_string,
                    '[',
                    '...',
                    ', ',
                    str(return_value_type_annotation),
                    ']'
                ))
            else:
                return ''.join((
                    subscribed_class_string,
                    '[',
                    '[',
                    ', '.join(str(parameter_type_annotation) for parameter_type_annotation in parameter_type_annotations),
                    ']',
                    ', ',
                    str(return_value_type_annotation),
                    ']'
                ))
        else:
            type_annotation_tuple_string_list: list[str] = [
                str(type_annotation) for type_annotation in self.type_annotation_tuple
            ]

            return ''.join((subscribed_class_string, '[', ', '.join(type_annotation_tuple_string_list), ']'))


class Union:
    __slots__ = ('type_annotation_frozenset',)

    def __init__(self, type_annotation_frozenset: frozenset['TypeshedTypeAnnotation']):
        self.type_annotation_frozenset = type_annotation_frozenset

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Union):
            return self.type_annotation_frozenset == other.type_annotation_frozenset
        return False

    def __hash__(self) -> int:
        return hash(self.type_annotation_frozenset)

    def __repr__(self) -> str:
        type_annotation_frozenset_string_list: list[str] = [str(type_annotation) for type_annotation in
                                                            self.type_annotation_frozenset]

        return ' | '.join(type_annotation_frozenset_string_list)


class RecursiveUnion:
    __slots__ = ('type_variable', 'type_annotation_frozenset')

    def __init__(self, type_variable: TypeshedTypeVariable, type_annotation_frozenset: frozenset[
        'TypeshedTypeAnnotation']):
        self.type_variable = type_variable
        self.type_annotation_frozenset = type_annotation_frozenset

    def __eq__(self, other: object) -> bool:
        if isinstance(other, RecursiveUnion):
            return self.type_variable == other.type_variable and self.type_annotation_frozenset == other.type_annotation_frozenset
        return False

    def __hash__(self) -> int:
        return hash((self.type_variable, self.type_annotation_frozenset))

    def __repr__(self) -> str:
        return f"RecursiveUnion(type_variable={self.type_variable}, type_annotation_frozenset={self.type_annotation_frozenset})"


TypeshedTypeAnnotation = typing.Union[
    TypeshedTypeVariable,
    TypeshedClass,
    Subscription,
    Union,
    RecursiveUnion
]


def iterate_type_variables_in_type_annotation(
        type_annotation: TypeshedTypeAnnotation
) -> Generator[TypeshedTypeVariable, None, None]:
    if isinstance(type_annotation, TypeshedTypeVariable):
        yield type_annotation
    elif isinstance(type_annotation, Subscription):
        for child_type_annotation in type_annotation.type_annotation_tuple:
            yield from iterate_type_variables_in_type_annotation(child_type_annotation)
    elif isinstance(type_annotation, Union):
        for child_type_annotation in type_annotation.type_annotation_frozenset:
            yield from iterate_type_variables_in_type_annotation(child_type_annotation)
    elif isinstance(type_annotation, RecursiveUnion):
        for child_type_annotation in type_annotation.type_annotation_frozenset:
            for type_variable in iterate_type_variables_in_type_annotation(child_type_annotation):
                if type_variable is not type_annotation.type_variable:
                    yield type_variable


def replace_type_variables_in_type_annotation(
        type_annotation: TypeshedTypeAnnotation,
        old_type_variable_to_new_type_annotation_dict: dict[
            TypeshedTypeVariable,
            TypeshedTypeAnnotation
        ]
) -> TypeshedTypeAnnotation:
    if isinstance(type_annotation, TypeshedTypeVariable):
        if type_annotation in old_type_variable_to_new_type_annotation_dict:
            return old_type_variable_to_new_type_annotation_dict[type_annotation]
        else:
            return type_annotation
    elif isinstance(type_annotation, Subscription):
        new_subscribed_class = type_annotation.subscribed_class
        new_type_annotation_list = [
            replace_type_variables_in_type_annotation(
                old_type_annotation,
                old_type_variable_to_new_type_annotation_dict)
            for old_type_annotation in type_annotation.type_annotation_tuple
        ]
        return Subscription(new_subscribed_class, tuple(new_type_annotation_list))
    elif isinstance(type_annotation, Union):
        new_type_annotation_list = [
            replace_type_variables_in_type_annotation(
                old_type_annotation,
                old_type_variable_to_new_type_annotation_dict
            )
            for old_type_annotation in type_annotation.type_annotation_frozenset
        ]
        return Union(frozenset(new_type_annotation_list))
    elif isinstance(type_annotation, RecursiveUnion):
        assert type_annotation.type_variable not in old_type_variable_to_new_type_annotation_dict

        new_type_annotation_list = [
            replace_type_variables_in_type_annotation(
                old_type_annotation,
                old_type_variable_to_new_type_annotation_dict
            )
            for old_type_annotation in type_annotation.type_annotation_frozenset
        ]
        return RecursiveUnion(type_annotation.type_variable, frozenset(new_type_annotation_list))
    else:
        return type_annotation


def subscribe(
        type_annotation: TypeshedTypeAnnotation,
        type_annotation_tuple: tuple[TypeshedTypeAnnotation, ...]
) -> TypeshedTypeAnnotation:
    # Do nothing for empty type annotation tuples
    if not type_annotation_tuple:
        return type_annotation

    # Subscribing a TypeshedClass creates a Subscription
    if isinstance(type_annotation, TypeshedClass):
        return Subscription(type_annotation, type_annotation_tuple)
    # Subscribing a Union creates a new Union if there are TypeVariable's within that union
    # >>> import typing
    # >>> T = typing.TypeVar('T')
    # >>> U = typing.TypeVar('U')
    # >>> (list[T] | set[T])[int]
    # list[int] | set[int]
    # >>> (list[T] | set[U])[int, str]
    # list[int] | set[str]
    # >>> (list[T] | list[T])[int]
    # list[int]
    elif isinstance(type_annotation, Union):
        type_variable_ordered_set: OrderedSet[TypeshedTypeVariable] = OrderedSet(
            iterate_type_variables_in_type_annotation(type_annotation))

        if type_variable_ordered_set:
            old_type_variable_to_new_type_annotation_dict: dict[
                TypeshedTypeVariable,
                TypeshedTypeAnnotation
            ] = {
                type_variable: type_annotation
                for type_variable, type_annotation
                in zip(type_variable_ordered_set, type_annotation_tuple)
            }

            subscribed_type_annotation_set: set[TypeshedTypeAnnotation] = {
                replace_type_variables_in_type_annotation(child_type_annotation,
                                                          old_type_variable_to_new_type_annotation_dict)
                for child_type_annotation in type_annotation.type_annotation_frozenset
            }

            if len(subscribed_type_annotation_set) > 1:
                return Union(frozenset(subscribed_type_annotation_set))
            else:
                return next(iter(subscribed_type_annotation_set))

        else:
            return type_annotation
    # Subscribing a Subscription creates a new Subscription if there are TypeVariable's within that Subscription
    # >>> import typing
    # >>> T = typing.TypeVar('T')
    # >>> U = typing.TypeVar('U')
    # >>> (list[T])[int]
    # list[int]
    # >>> (dict[T, U])[int, str]
    # dict[int, str]
    elif isinstance(type_annotation, Subscription):
        type_variable_ordered_set: OrderedSet[TypeshedTypeVariable] = OrderedSet(
            iterate_type_variables_in_type_annotation(type_annotation))

        if type_variable_ordered_set:
            old_type_variable_to_new_type_annotation_dict: dict[
                TypeshedTypeVariable,
                TypeshedTypeAnnotation
            ] = {
                type_variable: type_annotation
                for type_variable, type_annotation
                in zip(type_variable_ordered_set, type_annotation_tuple)
            }

            return replace_type_variables_in_type_annotation(type_annotation,
                                                             old_type_variable_to_new_type_annotation_dict)
        else:
            return type_annotation
    else:
        return type_annotation


def simplify_type_annotation(
        type_annotation: TypeshedTypeAnnotation
) -> TypeshedTypeAnnotation:
    # Non-simplifiable type annotations
    if isinstance(type_annotation, TypeshedTypeVariable):
        return type_annotation
    elif isinstance(type_annotation, TypeshedClass):
        # https://docs.python.org/3/library/typing.html#typing.LiteralString
        if type_annotation == TypeshedClass('typing', 'LiteralString'):
            return from_runtime_class(str)
        else:
            return type_annotation
    # Simplifiable type annotations
    elif isinstance(type_annotation, Subscription):
        subscribed_class = type_annotation.subscribed_class
        simplified_type_annotation_list = []
        for e in type_annotation.type_annotation_tuple:
            simplified_type_annotation_list.extend(expand_type_annotation(e))

        # https://docs.python.org/3/library/typing.html#typing.Annotated
        # https://docs.python.org/3/library/typing.html#typing.ClassVar
        # https://docs.python.org/3/library/typing.html#typing.Final
        # https://docs.python.org/3/library/typing.html#typing.NotRequired
        if subscribed_class in (
                TypeshedClass('typing', 'Annotated'),
                TypeshedClass('typing', 'ClassVar'),
                TypeshedClass('typing', 'Final'),
                TypeshedClass('typing', 'NotRequired'),
                TypeshedClass('typing', 'Required'),
        ):
            return simplify_type_annotation(simplified_type_annotation_list[0])
        # https://docs.python.org/3/library/typing.html#typing.Literal
        elif subscribed_class == TypeshedClass('typing', 'Literal'):
            return simplify_type_annotation(
                Union(
                    frozenset(simplified_type_annotation_list)
                )
            )
        # https://docs.python.org/3/library/typing.html#typing.Optional
        elif subscribed_class == TypeshedClass('typing', 'Optional'):
            simplified_type_annotation_list.append(from_runtime_class(type(None)))
            return simplify_type_annotation(Union(frozenset(simplified_type_annotation_list)))
        # https://docs.python.org/3/library/typing.html#typing.TypeGuard
        elif subscribed_class == TypeshedClass('typing', 'TypeGuard'):
            return from_runtime_class(bool)
        elif subscribed_class == TypeshedClass('typing', 'Union'):
            return simplify_type_annotation(Union(frozenset(simplified_type_annotation_list)))
        # https://docs.python.org/3/library/typing.html#annotating-tuples
        # To denote a tuple which could be of any length, and in which all elements are of the same type T, use tuple[T, ...].
        # Convert that to Sequence[T].
        elif (
                subscribed_class == TypeshedClass('builtins', 'tuple')
            and len(simplified_type_annotation_list) == 2
            and simplified_type_annotation_list[1] == from_runtime_class(type(Ellipsis))
        ):
            return subscribe(
                from_runtime_class(collections.abc.Sequence),
                (
                    simplified_type_annotation_list[0],
                )
            )
        else:
            return type_annotation
    elif isinstance(type_annotation, Union):
        simplified_type_annotation_set = set()

        for element in type_annotation.type_annotation_frozenset:
            # Simplify each element in the type annotation set
            simplified_element = simplify_type_annotation(element)

            # Flatten nested unions
            if isinstance(element, Union):
                simplified_type_annotation_set.update(simplified_element.type_annotation_frozenset)
            else:
                simplified_type_annotation_set.add(simplified_element)

        if len(simplified_type_annotation_set) == 1:
            return next(iter(simplified_type_annotation_set))
        else:
            return Union(frozenset(simplified_type_annotation_set))
    else:
        return type_annotation


def expand_type_annotation(type_annotation: TypeshedTypeAnnotation) -> Generator[TypeshedTypeAnnotation, None, None]:
    if isinstance(type_annotation, Subscription):
        subscribed_class = type_annotation.subscribed_class

        # https://docs.python.org/3/library/typing.html#typing.Concatenate
        if subscribed_class == TypeshedClass('typing', 'Concatenate'):
            yield from type_annotation.type_annotation_tuple
        # https://docs.python.org/3/library/typing.html#typing.Unpack
        elif subscribed_class == TypeshedClass('typing', 'Unpack'):
            yield TypeshedClass('typing', 'Any')
            yield from_runtime_class(type(Ellipsis))
        else:
            yield type_annotation
    else:
        yield type_annotation


# Typeshed Name Lookup Result

class TypeshedModule:
    __slots__ = ('module_name',)

    def __init__(
            self,
            module_name: str
    ):
        self.module_name: str = module_name

    def __eq__(self, other: object) -> bool:
        if isinstance(
                other,
                TypeshedModule
        ) and self.module_name == other.module_name:
            return True
        else:
            return False

    def __hash__(self) -> int:
        return hash((self.module_name,))

    def __str__(self) -> str:
        return f'{self.module_name}'

    def __repr__(self) -> str:
        return f"TypeshedModule(module_name='{self.module_name}')"


class TypeshedFunction:
    __slots__ = ('module_name', 'function_name')

    def __init__(self, module_name: str, function_name: str):
        self.module_name = module_name
        self.function_name = function_name

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeshedFunction):
            return (
                    self.module_name == other.module_name
                    and self.function_name == other.function_name
            )
        return False

    def __hash__(self) -> int:
        return hash((self.module_name, self.function_name))

    def __repr__(self) -> str:
        return f"TypeshedFunction(module_name={self.module_name}, function_name={self.function_name})"


class TypeshedMethod:
    __slots__ = ('module_name', 'class_name', 'function_name')

    def __init__(self, module_name: str, class_name: str, function_name: str):
        self.module_name = module_name
        self.class_name = class_name
        self.function_name = function_name

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeshedMethod):
            return (
                    self.module_name == other.module_name
                    and self.class_name == other.class_name
                    and self.function_name == other.function_name
            )
        return False

    def __hash__(self) -> int:
        return hash((self.module_name, self.class_name, self.function_name))

    def __repr__(self) -> str:
        return f"TypeshedMethod(module_name={self.module_name}, class_name={self.class_name}, function_name={self.function_name})"


TypeshedNameLookupResult = typing.Union[
    TypeshedTypeAnnotation,
    TypeshedModule,
    TypeshedFunction,
    TypeshedMethod
]


# Typeshed Function Definition

class TypeshedFunctionDefinition:
    __slots__ = (
        'type_variable_list',
        'parameter_type_annotation_list',
        'vararg_type_annotation',
        'kwonlyargs_name_to_type_annotation_dict',
        'kwarg_type_annotation',
        'return_value_type_annotation'
    )

    def __init__(
            self,
            type_variable_list: list[TypeshedTypeVariable],
            parameter_type_annotation_list: list[TypeshedTypeAnnotation],
            vararg_type_annotation: Optional[TypeshedTypeAnnotation],
            kwonlyargs_name_to_type_annotation_dict: dict[str, TypeshedTypeAnnotation],
            kwarg_type_annotation: Optional[TypeshedTypeAnnotation],
            return_value_type_annotation: TypeshedTypeAnnotation
    ):
        self.type_variable_list: list[TypeshedTypeVariable] = type_variable_list
        self.parameter_type_annotation_list: list[TypeshedTypeAnnotation] = parameter_type_annotation_list
        self.vararg_type_annotation: Optional[TypeshedTypeAnnotation] = vararg_type_annotation
        self.kwonlyargs_name_to_type_annotation_dict: dict[
            str, TypeshedTypeAnnotation] = kwonlyargs_name_to_type_annotation_dict
        self.kwarg_type_annotation: Optional[TypeshedTypeAnnotation] = kwarg_type_annotation
        self.return_value_type_annotation: TypeshedTypeAnnotation = return_value_type_annotation

    def __repr__(self):
        return f"FunctionDefinition(type_variable_list={self.type_variable_list}, parameter_type_annotation_list={self.parameter_type_annotation_list}, vararg_type_annotation={self.vararg_type_annotation}, kwonlyargs_name_to_type_annotation_dict={self.kwonlyargs_name_to_type_annotation_dict}, kwarg_type_annotation={self.kwarg_type_annotation}, return_value_type_annotation={self.return_value_type_annotation})"

    def __eq__(self, other):
        if not isinstance(other, TypeshedFunctionDefinition):
            return False

        return (self.type_variable_list == other.type_variable_list and
                self.parameter_type_annotation_list == other.parameter_type_annotation_list and
                self.vararg_type_annotation == other.vararg_type_annotation and
                self.kwonlyargs_name_to_type_annotation_dict == other.kwonlyargs_name_to_type_annotation_dict and
                self.kwarg_type_annotation == other.kwarg_type_annotation and
                self.return_value_type_annotation == other.return_value_type_annotation)


def instantiate_type_variables_in_function_definition(
        function_definition: TypeshedFunctionDefinition,
        type_annotation_list: list[TypeshedTypeAnnotation]
) -> TypeshedFunctionDefinition:
    assert len(type_annotation_list) >= len(function_definition.type_variable_list)

    old_type_variable_to_new_type_annotation_dict = {
        old_type_variable: new_type_annotation
        for old_type_variable, new_type_annotation in zip(function_definition.type_variable_list, type_annotation_list)
    }

    new_function_definition_type_variable_list = [
        new_type_annotation
        for new_type_annotation in old_type_variable_to_new_type_annotation_dict.values()
        if isinstance(new_type_annotation, TypeshedTypeVariable)
    ]

    new_function_definition_parameter_type_annotation_list = [
        replace_type_variables_in_type_annotation(
            old_parameter_type_annotation,
            old_type_variable_to_new_type_annotation_dict
        )
        for old_parameter_type_annotation in function_definition.parameter_type_annotation_list
    ]

    new_function_definition_vararg_type_annotation = replace_type_variables_in_type_annotation(
        function_definition.vararg_type_annotation,
        old_type_variable_to_new_type_annotation_dict
    )

    new_function_definition_kwonlyargs_name_to_type_annotation_dict = {
        kwonlyargs_name: replace_type_variables_in_type_annotation(
            old_kwonlyargs_type_annotation,
            old_type_variable_to_new_type_annotation_dict
        )
        for kwonlyargs_name, old_kwonlyargs_type_annotation
        in function_definition.kwonlyargs_name_to_type_annotation_dict.items()
    }

    new_function_definition_kwarg_type_annotation = replace_type_variables_in_type_annotation(
        function_definition.kwarg_type_annotation,
        old_type_variable_to_new_type_annotation_dict
    )

    new_function_definition_return_value_type_annotation = replace_type_variables_in_type_annotation(
        function_definition.return_value_type_annotation,
        old_type_variable_to_new_type_annotation_dict
    )

    return TypeshedFunctionDefinition(
        new_function_definition_type_variable_list,
        new_function_definition_parameter_type_annotation_list,
        new_function_definition_vararg_type_annotation,
        new_function_definition_kwonlyargs_name_to_type_annotation_dict,
        new_function_definition_kwarg_type_annotation,
        new_function_definition_return_value_type_annotation
    )


def get_comprehensive_type_annotations_for_parameters_and_return_values(
        function_definitions: list[TypeshedFunctionDefinition]
):
    parameter_index_to_type_annotation_set: defaultdict[int, set[TypeshedTypeAnnotation]] = defaultdict(set)
    return_value_type_annotation_set: set[TypeshedTypeAnnotation] = set()

    for function_definition in function_definitions:
        for i, parameter_type_annotation in enumerate(function_definition.parameter_type_annotation_list):
            parameter_index_to_type_annotation_set[i].add(parameter_type_annotation)
        return_value_type_annotation_set.add(function_definition.return_value_type_annotation)

    simplified_parameter_type_annotation_list: list[TypeshedTypeAnnotation] = []

    if parameter_index_to_type_annotation_set:
        number_of_parameters = max(parameter_index_to_type_annotation_set.keys()) + 1

        for i in range(number_of_parameters):
            simplified_parameter_type_annotation = simplify_type_annotation(
                Union(
                    frozenset(
                        parameter_index_to_type_annotation_set[i]
                    )
                )
            )
            simplified_parameter_type_annotation_list.append(simplified_parameter_type_annotation)

    simplified_return_value_type_annotation = simplify_type_annotation(
        Union(
            frozenset(
                return_value_type_annotation_set
            )
        )
    )

    return simplified_parameter_type_annotation_list, simplified_return_value_type_annotation


# Typeshed Class Definition

class TypeshedClassDefinition:
    __slots__ = (
        'type_variable_list',
        'method_name_to_method_list_dict',
        'class_variable_name_to_type_annotation_dict'
    )

    def __init__(
            self,
            type_variable_list: list[TypeshedTypeVariable],
            method_name_to_method_list_dict: dict[str, list[TypeshedFunctionDefinition]],
            class_variable_name_to_type_annotation_dict: dict[str, TypeshedTypeAnnotation]
    ):
        self.type_variable_list: list[TypeshedTypeVariable] = type_variable_list
        self.method_name_to_method_list_dict: dict[
            str, list[TypeshedFunctionDefinition]] = method_name_to_method_list_dict
        self.class_variable_name_to_type_annotation_dict: dict[
            str, TypeshedTypeAnnotation] = class_variable_name_to_type_annotation_dict

    def __eq__(self, other):
        if not isinstance(other, TypeshedClassDefinition):
            return False

        return (self.type_variable_list == other.type_variable_list and
                self.method_name_to_method_list_dict == other.method_name_to_method_list_dict and
                self.class_variable_name_to_type_annotation_dict == other.class_variable_name_to_type_annotation_dict)
        
    def __repr__(self):
        return f"ClassDefinition(type_variable_list={self.type_variable_list}, method_name_to_method_list_dict={self.method_name_to_method_list_dict}, class_variable_name_to_type_annotation_dict={self.class_variable_name_to_type_annotation_dict})"


def get_attributes_in_class_definition(
        class_definition: TypeshedClassDefinition
) -> set[str]:
    attribute_set: set[str] = set()

    attribute_set.update(class_definition.class_variable_name_to_type_annotation_dict.keys())
    attribute_set.update(class_definition.method_name_to_method_list_dict.keys())

    return attribute_set


def get_type_annotation_of_self(
        class_: TypeshedClass,
        type_variable_list: list[TypeshedTypeVariable]
) -> TypeshedTypeAnnotation:
    if type_variable_list:
        return subscribe(class_, tuple(type_variable_list))
    else:
        return class_


def instantiate_type_variables_in_class_definition(
        class_definition: TypeshedClassDefinition,
        type_annotation_list: list[TypeshedTypeAnnotation]
) -> TypeshedClassDefinition:
    assert len(type_annotation_list) >= len(class_definition.type_variable_list)

    old_type_variable_to_new_type_annotation_dict = {
        old_type_variable: new_type_annotation
        for old_type_variable, new_type_annotation in zip(class_definition.type_variable_list, type_annotation_list)
    }

    new_type_variable_list = [
        new_type_annotation
        for new_type_annotation in old_type_variable_to_new_type_annotation_dict.values()
        if isinstance(new_type_annotation, TypeshedTypeVariable)
    ]

    new_method_name_to_method_list_dict = dict()

    for method_name, method_list in class_definition.method_name_to_method_list_dict.items():
        new_method_name = method_name
        new_method_list = list()

        for method in method_list:
            # Create method_level_old_type_variable_to_new_type_annotation_dict
            method_level_old_type_variable_to_new_type_annotation_dict = \
                old_type_variable_to_new_type_annotation_dict.copy()
            for method_level_type_variable in method.type_variable_list:
                method_level_old_type_variable_to_new_type_annotation_dict[method_level_type_variable] = \
                    method_level_type_variable

            new_method_type_variable_list = method.type_variable_list

            new_method_parameter_type_annotation_list = [
                replace_type_variables_in_type_annotation(
                    old_parameter_type_annotation,
                    method_level_old_type_variable_to_new_type_annotation_dict
                )
                for old_parameter_type_annotation in method.parameter_type_annotation_list
            ]

            new_method_vararg_type_annotation = replace_type_variables_in_type_annotation(
                method.vararg_type_annotation,
                method_level_old_type_variable_to_new_type_annotation_dict
            )

            new_method_kwonlyargs_name_to_type_annotation_dict = {
                kwonlyargs_name: replace_type_variables_in_type_annotation(
                    old_kwonlyargs_type_annotation,
                    method_level_old_type_variable_to_new_type_annotation_dict
                )
                for kwonlyargs_name, old_kwonlyargs_type_annotation in
                method.kwonlyargs_name_to_type_annotation_dict.items()
            }

            new_method_kwarg_type_annotation = replace_type_variables_in_type_annotation(
                method.kwarg_type_annotation,
                method_level_old_type_variable_to_new_type_annotation_dict
            )

            new_method_return_value_type_annotation = replace_type_variables_in_type_annotation(
                method.return_value_type_annotation,
                method_level_old_type_variable_to_new_type_annotation_dict
            )

            new_method = TypeshedFunctionDefinition(
                new_method_type_variable_list,
                new_method_parameter_type_annotation_list,
                new_method_vararg_type_annotation,
                new_method_kwonlyargs_name_to_type_annotation_dict,
                new_method_kwarg_type_annotation,
                new_method_return_value_type_annotation
            )

            new_method_list.append(new_method)

        new_method_name_to_method_list_dict[new_method_name] = new_method_list

    new_class_variable_name_to_type_annotation_dict = dict()

    for class_variable_name, type_annotation in class_definition.class_variable_name_to_type_annotation_dict.items():
        new_class_variable_name = class_variable_name

        new_type_annotation = replace_type_variables_in_type_annotation(
            type_annotation,
            old_type_variable_to_new_type_annotation_dict
        )

        new_class_variable_name_to_type_annotation_dict[new_class_variable_name] = new_type_annotation

    return TypeshedClassDefinition(
        new_type_variable_list,
        new_method_name_to_method_list_dict,
        new_class_variable_name_to_type_annotation_dict
    )


def replace_typing_self_in_type_annotation(
        type_annotation: TypeshedTypeAnnotation,
        type_annotation_of_self: TypeshedTypeAnnotation
) -> TypeshedTypeAnnotation:
    if isinstance(type_annotation, TypeshedClass):
        if type_annotation == TypeshedClass('typing', 'Self'):
            return type_annotation_of_self
        else:
            return type_annotation
    elif isinstance(type_annotation, Subscription):
        new_subscribed_class = replace_typing_self_in_type_annotation(
            type_annotation.subscribed_class,
            type_annotation_of_self
        )

        new_type_annotation_list = [
            replace_typing_self_in_type_annotation(
                old_type_annotation,
                type_annotation_of_self
            )
            for old_type_annotation in type_annotation.type_annotation_tuple
        ]

        return Subscription(new_subscribed_class, tuple(new_type_annotation_list))
    elif isinstance(type_annotation, Union):
        new_type_annotation_list = [
            replace_typing_self_in_type_annotation(
                old_type_annotation,
                type_annotation_of_self
            )
            for old_type_annotation in type_annotation.type_annotation_frozenset
        ]
        return Union(frozenset(new_type_annotation_list))
    elif isinstance(type_annotation, RecursiveUnion):
        assert type_annotation.type_variable not in old_type_variable_to_new_type_annotation_dict

        new_type_annotation_list = [
            replace_typing_self_in_type_annotation(
                old_type_annotation,
                type_annotation_of_self
            )
            for old_type_annotation in type_annotation.type_annotation_frozenset
        ]
        return RecursiveUnion(type_annotation.type_variable, frozenset(new_type_annotation_list))
    else:
        return type_annotation


def replace_typing_self_in_class_definition(
        class_definition: TypeshedClassDefinition,
        type_annotation_of_self: TypeshedTypeAnnotation
) -> TypeshedClassDefinition:
    new_type_variable_list = class_definition.type_variable_list

    new_method_name_to_method_list_dict = dict()

    for method_name, method_list in class_definition.method_name_to_method_list_dict.items():
        new_method_name = method_name
        new_method_list = list()

        for method in method_list:
            new_method_type_variable_list = method.type_variable_list

            new_method_parameter_type_annotation_list = [
                replace_typing_self_in_type_annotation(
                    old_parameter_type_annotation,
                    type_annotation_of_self
                )
                for old_parameter_type_annotation in method.parameter_type_annotation_list
            ]

            new_method_vararg_type_annotation = replace_typing_self_in_type_annotation(
                method.vararg_type_annotation,
                type_annotation_of_self
            )

            new_method_kwonlyargs_name_to_type_annotation_dict = {
                kwonlyargs_name: replace_typing_self_in_type_annotation(
                    old_kwonlyargs_type_annotation,
                    type_annotation_of_self
                )
                for kwonlyargs_name, old_kwonlyargs_type_annotation in
                method.kwonlyargs_name_to_type_annotation_dict.items()
            }

            new_method_kwarg_type_annotation = replace_typing_self_in_type_annotation(
                method.kwarg_type_annotation,
                type_annotation_of_self
            )

            new_method_return_value_type_annotation = replace_typing_self_in_type_annotation(
                method.return_value_type_annotation,
                type_annotation_of_self
            )

            new_method = TypeshedFunctionDefinition(
                new_method_type_variable_list,
                new_method_parameter_type_annotation_list,
                new_method_vararg_type_annotation,
                new_method_kwonlyargs_name_to_type_annotation_dict,
                new_method_kwarg_type_annotation,
                new_method_return_value_type_annotation
            )

            new_method_list.append(new_method)

        new_method_name_to_method_list_dict[new_method_name] = new_method_list

    new_class_variable_name_to_type_annotation_dict = dict()

    for class_variable_name, type_annotation in class_definition.class_variable_name_to_type_annotation_dict.items():
        new_class_variable_name = class_variable_name

        new_type_annotation = replace_typing_self_in_type_annotation(
            type_annotation,
            type_annotation_of_self
        )

        new_class_variable_name_to_type_annotation_dict[new_class_variable_name] = new_type_annotation

    return TypeshedClassDefinition(
        new_type_variable_list,
        new_method_name_to_method_list_dict,
        new_class_variable_name_to_type_annotation_dict
    )
