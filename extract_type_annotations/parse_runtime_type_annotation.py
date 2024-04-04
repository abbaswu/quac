"""
Parse runtime type annotation.

coverage run --source parse_runtime_type_annotation parse_runtime_type_annotation.py && coverage html
"""

import abc
import builtins
import collections.abc
import types
import typing
import pudb

from type_inference_result import TypeInferenceResult, TypeInferenceClass


runtime_objects_to_type_inference_class_mapping: dict[typing.Any, TypeInferenceClass] = {
    None: TypeInferenceClass(
        'builtins',
        'NoneType'
    ),
    Ellipsis: TypeInferenceClass(
        'builtins',
        'ellipsis'
    ),
    typing.Any: TypeInferenceClass(
        'typing',
        'Any'
    ),
    typing.Union: TypeInferenceClass(
        'typing',
        'Union'
    ),
}


def parse_runtime_type_annotation(
    runtime_type_annotation: typing.Any,
    module: types.ModuleType
) -> TypeInferenceResult:
    # None, Ellipsis, typing.Any, typing.Union
    # Handle as class
    if runtime_type_annotation in runtime_objects_to_type_inference_class_mapping:
        return TypeInferenceResult(
            runtime_objects_to_type_inference_class_mapping[runtime_type_annotation]
        )
    # list, collections.abc.Callable
    elif type(runtime_type_annotation) in (type, abc.ABCMeta):
        return TypeInferenceResult(
            TypeInferenceClass(
                runtime_type_annotation.__module__,
                runtime_type_annotation.__name__
            )
        )
    # list | int
    elif type(runtime_type_annotation) is types.UnionType:
        arg_type_inference_result_list: list[TypeInferenceResult] = [
            parse_runtime_type_annotation(arg, module) for arg in runtime_type_annotation.__args__
        ]

        return TypeInferenceResult(
            TypeInferenceClass(
                'typing',
                'Union'
            ),
            tuple(arg_type_inference_result_list)
        )
    # typing.List, typing.Tuple, typing.Callable
    elif type(runtime_type_annotation) in (
            typing._SpecialGenericAlias,
            typing._TupleType,
            typing._CallableType
    ):
        return parse_runtime_type_annotation(runtime_type_annotation.__origin__, module)
    # list[pathman._impl.s3.S3Path], typing.List[pathman._impl.s3.S3Path], tuple[int, ...], typing.Tuple[int, ...]
    # collections.abc.Callable[[int, str], Any], typing.Callable[[int, str], Any]
    # typing.Union[int, str]
    elif type(runtime_type_annotation) in (
            types.GenericAlias,
            typing._GenericAlias,
            typing._CallableGenericAlias,
            collections.abc._CallableGenericAlias,
            typing._UnionGenericAlias
    ):
        origin_type_inference_result = parse_runtime_type_annotation(runtime_type_annotation.__origin__, module)

        arg_type_inference_result_list: list[TypeInferenceResult] = [
            parse_runtime_type_annotation(arg, module) for arg in runtime_type_annotation.__args__
        ]

        return TypeInferenceResult(
            origin_type_inference_result.type_inference_class,
            tuple(arg_type_inference_result_list)
        )
    elif type(runtime_type_annotation) is str:
        eval_result = eval(runtime_type_annotation, module.__dict__)
        return parse_runtime_type_annotation(eval_result, module)
    elif type(runtime_type_annotation) is typing.ForwardRef:
        eval_result = eval(runtime_type_annotation.__forward_arg__, module.__dict__)
        return parse_runtime_type_annotation(eval_result, module)
    else:
        assert False, f'Unhandled runtime type annotation: {runtime_type_annotation} (type: {type(runtime_type_annotation)})'


if __name__ == '__main__':
    import type_inference_result

    assert parse_runtime_type_annotation(typing.Union, builtins) == TypeInferenceResult(
        TypeInferenceClass(
            'typing',
            'Union'
        )
    )

    assert parse_runtime_type_annotation(int | str, builtins) == parse_runtime_type_annotation(typing.Union[int, str], builtins) == TypeInferenceResult(
        TypeInferenceClass(
            'typing',
            'Union'
        ),
        (
            TypeInferenceResult(
                TypeInferenceClass(
                    'builtins',
                    'int'
                )
            ),
            TypeInferenceResult(
                TypeInferenceClass(
                    'builtins',
                    'str'
                )
            )
        )
    )

    assert parse_runtime_type_annotation(typing.List, builtins) == TypeInferenceResult(
        TypeInferenceClass(
            'builtins',
            'list'
        )
    )

    assert parse_runtime_type_annotation('tuple[TypeInferenceResult, ...]', type_inference_result) == TypeInferenceResult(
        TypeInferenceClass(
            'builtins',
            'tuple'
        ),
        (
            TypeInferenceResult(
                TypeInferenceClass(
                    'type_inference_result',
                    'TypeInferenceResult'
                )
            ),
            TypeInferenceResult(
                TypeInferenceClass(
                    'builtins',
                    'ellipsis'
                )
            )
        )
    )
