from .type_definitions import TypeshedClass, TypeshedClassDefinition, TypeshedFunctionDefinition, from_runtime_class

# We treat `typing._SpecialForm`'s as classes to allow them to be subscribed
special_form_module_name_name_tuple_to_type_annotation: dict[
    tuple[str, str],
    TypeshedClass
] = {
    ('typing', 'Annotated'): TypeshedClass('typing', 'Annotated'),
    ('typing_extensions', 'Annotated'): TypeshedClass('typing', 'Annotated'),
    ('typing', 'Any'): TypeshedClass('typing', 'Any'),
    ('typing', 'Callable'): TypeshedClass('typing', 'Callable'),
    ('typing', 'ChainMap'): TypeshedClass('collections', 'ChainMap'),
    ('typing', 'ClassVar'): TypeshedClass('typing', 'ClassVar'),
    ('typing', 'Concatenate'): TypeshedClass('typing', 'Concatenate'),
    ('typing_extensions', 'Concatenate'): TypeshedClass('typing', 'Concatenate'),
    ('typing', 'Counter'): TypeshedClass('collections', 'Counter'),
    ('typing', 'DefaultDict'): TypeshedClass('collections', 'defaultdict'),
    ('typing', 'Deque'): TypeshedClass('collections', 'deque'),
    ('typing', 'Dict'): TypeshedClass('builtins', 'dict'),
    ('typing', 'Final'): TypeshedClass('typing', 'Final'),
    ('typing_extensions', 'Final'): TypeshedClass('typing', 'Final'),
    ('typing', 'FrozenSet'): TypeshedClass('builtins', 'frozenset'),
    ('typing', 'Generic'): TypeshedClass('typing', 'Generic'),
    ('typing', 'List'): TypeshedClass('builtins', 'list'),
    ('typing', 'Literal'): TypeshedClass('typing', 'Literal'),
    ('typing_extensions', 'Literal'): TypeshedClass('typing', 'Literal'),
    ('typing', 'LiteralString'): TypeshedClass('typing', 'LiteralString'),
    ('typing_extensions', 'LiteralString'): TypeshedClass('typing', 'LiteralString'),
    ('typing', 'Never'): TypeshedClass('typing', 'Never'),
    ('typing_extensions', 'Never'): TypeshedClass('typing', 'Never'),
    ('typing', 'NoReturn'): TypeshedClass('typing', 'Never'),
    ('typing', 'NotRequired'): TypeshedClass('typing', 'NotRequired'),
    ('typing_extensions', 'NotRequired'): TypeshedClass('typing', 'NotRequired'),
    ('typing', 'Optional'): TypeshedClass('typing', 'Optional'),
    ('typing', 'OrderedDict'): TypeshedClass('builtins', 'dict'),
    ('typing', 'Protocol'): TypeshedClass('typing', 'Protocol'),
    ('typing_extensions', 'Protocol'): TypeshedClass('typing', 'Protocol'),
    ('typing', 'Required'): TypeshedClass('typing', 'Required'),
    ('typing_extensions', 'Required'): TypeshedClass('typing', 'Required'),
    ('typing', 'Self'): TypeshedClass('typing', 'Self'),
    ('typing_extensions', 'Self'): TypeshedClass('typing', 'Self'),
    ('_typeshed', 'Self'): TypeshedClass('typing', 'Self'),
    ('typing', 'Set'): TypeshedClass('builtins', 'set'),
    ('typing', 'Tuple'): TypeshedClass('builtins', 'tuple'),
    ('typing', 'Type'): TypeshedClass('builtins', 'type'),
    ('typing', 'TypeAlias'): TypeshedClass('typing', 'TypeAlias'),
    ('typing_extensions', 'TypeAlias'): TypeshedClass('typing', 'TypeAlias'),
    ('typing', 'TypeGuard'): TypeshedClass('typing', 'TypeGuard'),
    ('typing_extensions', 'TypeGuard'): TypeshedClass('typing', 'TypeGuard'),
    ('typing', 'TypedDict'): TypeshedClass('typing', 'TypedDict'),
    ('typing_extensions', 'TypedDict'): TypeshedClass('typing', 'TypedDict'),
    ('typing', 'Union'): TypeshedClass('typing', 'Union'),
    ('typing', 'Unpack'): TypeshedClass('typing', 'Unpack'),
    ('typing_extensions', 'Unpack'): TypeshedClass('typing', 'Unpack'),
}

special_form_typeshed_class_to_typeshed_class_definition: dict[TypeshedClass, TypeshedClassDefinition] = {
    from_runtime_class(type(None)): TypeshedClassDefinition(
        [],
        {
            '__bool__': [TypeshedFunctionDefinition(
                [],
                [TypeshedClass('typing', 'Any')],
                None,
                dict(),
                None,
                from_runtime_class(bool)
            )]
        },
        dict()
    )
}
