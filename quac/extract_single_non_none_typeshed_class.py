import typing

from typeshed_client_ex.type_definitions import (
    TypeshedTypeAnnotation,
    TypeshedClass,
    Subscription,
    Union,
    RecursiveUnion,
    from_runtime_class,
    to_runtime_class,
    TypeshedClassDefinition,
    get_comprehensive_type_annotations_for_parameters_and_return_values
)


NONETYPE_TYPESHED_CLASS = from_runtime_class(type(None))


def iterate_typeshed_classes(typeshed_type_annotation: TypeshedTypeAnnotation) -> typing.Iterator[TypeshedClass]:
    if isinstance(typeshed_type_annotation, TypeshedClass):
        yield typeshed_type_annotation
    elif isinstance(typeshed_type_annotation, Subscription):
        yield typeshed_type_annotation.subscribed_class
    elif isinstance(typeshed_type_annotation, (Union, RecursiveUnion)):
        for child_type_annotation in typeshed_type_annotation.type_annotation_frozenset:
            yield from iterate_typeshed_classes(child_type_annotation)


def extract_single_non_none_typeshed_class(
    typeshed_type_annotation: TypeshedTypeAnnotation
) -> typing.Optional[TypeshedClass]:
    typeshed_class_set: set[TypeshedClass] = set(iterate_typeshed_classes(typeshed_type_annotation)) - {NONETYPE_TYPESHED_CLASS}
    if len(typeshed_class_set) == 1:
        return next(iter(typeshed_class_set))
    else:
        return None
