from ignored_attributes import IGNORED_ATTRIBUTES
from typeshed_client_ex.type_definitions import TypeshedClassDefinition


def get_attributes_in_typeshed_class_definition(
        typeshed_class_definition: TypeshedClassDefinition
) -> set[str]:
    attribute_set: set[str] = set()

    attribute_set.update(typeshed_class_definition.class_variable_name_to_type_annotation_dict.keys())
    attribute_set.update(typeshed_class_definition.method_name_to_method_list_dict.keys())

    return attribute_set - IGNORED_ATTRIBUTES
