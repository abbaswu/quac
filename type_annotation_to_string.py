import abc
import collections.abc
import types
import typing
import pdb


# TODO: structured type annotations
def type_annotation_to_string(
    type_annotation: type | abc.ABCMeta | types.UnionType | types.GenericAlias | typing._GenericAlias | collections.abc._CallableGenericAlias | typing._CallableGenericAlias | typing._SpecialGenericAlias | typing._TupleType | typing._CallableType | typing._SpecialForm | typing.TypeVar | types.EllipsisType | None
) -> str:
    # type_annotation: None
    # type_annotation: builtins.NoneType
    if type_annotation is None or type_annotation is type(None):
        return 'None'
    # type_annotation: ...
    # type_annotation: Ellipsis
    elif type_annotation is Ellipsis:
        return '...'
    # type_annotation: list
    # type_annotation: collections.abc.Callable
    elif type(type_annotation) in (type, abc.ABCMeta):
        return f'{type_annotation.__module__}.{type_annotation.__name__}'
    # type_annotation: list | int
    elif type(type_annotation) is types.UnionType:
        arg_string_list: list[str] = []
        for arg in type_annotation.__args__:
            arg_string_list.append(type_annotation_to_string(arg))
        
        return ' | '.join(arg_string_list)
    # type_annotation: list[pathman._impl.s3.S3Path]
    # type_annotation: typing.List[pathman._impl.s3.S3Path]
    # type_annotation: tuple[int, ...]
    # type_annotation: typing.Tuple[int, ...]
    elif type(type_annotation) in (types.GenericAlias, typing._GenericAlias):
        origin_string: str = type_annotation_to_string(type_annotation.__origin__)

        arg_string_list: list[str] = [type_annotation_to_string(arg) for arg in type_annotation.__args__]

        return ''.join((origin_string, '[', ', '.join(arg_string_list), ']'))
    # type_annotation: collections.abc.Callable[[int, str], Any]
    # type_annotation: typing.Callable[[int, str], Any]
    elif type(type_annotation) in (collections.abc._CallableGenericAlias, typing._CallableGenericAlias):
        origin_string: str = type_annotation_to_string(type_annotation.__origin__)
        
        *parameter_type_annotations, return_value_type_annotation = type_annotation.__args__

        parameter_type_annotation_string_list: list[str] = [
            type_annotation_to_string(parameter_type_annotation)
            for parameter_type_annotation in parameter_type_annotations
        ]

        parameter_type_annotation_string: str = ''.join(('[', ', '.join(parameter_type_annotation_string_list), ']'))

        return_value_type_annotation_string: str = type_annotation_to_string(return_value_type_annotation)

        return ''.join((origin_string, '[', ', '.join((parameter_type_annotation_string, return_value_type_annotation_string)), ']'))
    # type_annotation: typing.List
    # type_annotation: typing.Tuple
    # type_annotation: typing.Callable
    elif type(type_annotation) in (typing._SpecialGenericAlias, typing._TupleType, typing._CallableType):
        return type_annotation_to_string(type_annotation.__origin__)
    # type_annotation: typing.Any
    elif type(type_annotation) is typing._SpecialForm:
        return str(type_annotation)
    # type_annotation: ~_TS3Path
    elif type(type_annotation) is typing.TypeVar:
        return type_annotation_to_string(type_annotation.__bound__)
    else:
        pdb.set_trace()
