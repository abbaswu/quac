import ast
import logging
import typing

from get_comprehensive_dict_for_runtime_class import get_comprehensive_dict_for_runtime_class
from type_definitions import (
    RuntimeTerm,
    Module,
    RuntimeClass,
    Instance,
    UnwrappedRuntimeFunction,
    FunctionDefinition,
    UnboundMethod,
    BoundMethod
)
from unwrap import unwrap


def get_attribute_access_result(
    runtime_term: RuntimeTerm,
    attribute_name: str,
    unwrapped_runtime_functions_to_named_function_definitions: typing.Mapping[UnwrappedRuntimeFunction, FunctionDefinition]
) -> typing.Optional[RuntimeTerm]:
    attribute_access_result: typing.Optional[RuntimeTerm] = None

    if isinstance(runtime_term, Module):
        runtime_term_dict = runtime_term.__dict__
        if attribute_name in runtime_term_dict:
            attribute = runtime_term_dict[attribute_name]
            unwrapped_attribute = unwrap(attribute)

            # Module -> Module
            if isinstance(unwrapped_attribute, Module):
                attribute_access_result = unwrapped_attribute
            # Module -> Class
            elif isinstance(unwrapped_attribute, RuntimeClass):
                attribute_access_result = unwrapped_attribute
            # Module -> Function
            elif isinstance(unwrapped_attribute, UnwrappedRuntimeFunction):
                # Function defined within the scope of the project
                if unwrapped_attribute in unwrapped_runtime_functions_to_named_function_definitions:
                    attribute_access_result = unwrapped_runtime_functions_to_named_function_definitions[unwrapped_attribute]
                elif getattr(unwrapped_attribute, '__module__', None) is not None and getattr(unwrapped_attribute, '__name__', None) is not None: # Guard against things such as random.random which is not actually a function
                    attribute_access_result = unwrapped_attribute
            # Module -> Instance
            elif not callable(unwrapped_attribute):
                attribute_access_result = Instance(type(unwrapped_attribute))
        else:
            logging.error('Cannot access attribute `%s` in module %s!', attribute_name, runtime_term)
    elif isinstance(runtime_term, RuntimeClass):
        runtime_term_dict = get_comprehensive_dict_for_runtime_class(runtime_term)
        if attribute_name in runtime_term_dict:
            attribute = runtime_term_dict[attribute_name]
            unwrapped_attribute = unwrap(attribute)

            # Class -> UnboundMethod
            if isinstance(unwrapped_attribute, UnwrappedRuntimeFunction):
                # Function defined within the scope of the project
                if unwrapped_attribute in unwrapped_runtime_functions_to_named_function_definitions:
                    attribute_access_result = UnboundMethod(
                        runtime_term,
                        unwrapped_runtime_functions_to_named_function_definitions[unwrapped_attribute]
                    )
                else:
                    attribute_access_result = UnboundMethod(
                        runtime_term,
                        unwrapped_attribute
                    )
            # Class -> Instance
            elif not callable(unwrapped_attribute):
                attribute_access_result = Instance(type(unwrapped_attribute))
        else:
            logging.error('Cannot access attribute `%s` in class %s!', attribute_name, runtime_term)
    elif isinstance(runtime_term, Instance):
        runtime_term_class_dict = get_comprehensive_dict_for_runtime_class(runtime_term.class_)
        if attribute_name in runtime_term_class_dict:
            attribute = runtime_term_class_dict[attribute_name]
            is_staticmethod = isinstance(attribute, staticmethod)
            unwrapped_attribute = unwrap(attribute)

            # Instance -> UnboundMethod
            # Instance -> BoundMethod
            if isinstance(unwrapped_attribute, UnwrappedRuntimeFunction):
                if is_staticmethod:
                    # Function defined within the scope of the project
                    if unwrapped_attribute in unwrapped_runtime_functions_to_named_function_definitions:
                        attribute_access_result = UnboundMethod(
                            runtime_term.class_,
                            unwrapped_runtime_functions_to_named_function_definitions[unwrapped_attribute]
                        )
                    else:
                        attribute_access_result = UnboundMethod(
                            runtime_term.class_,
                            unwrapped_attribute
                        )
                else:
                    # Function defined within the scope of the project
                    if unwrapped_attribute in unwrapped_runtime_functions_to_named_function_definitions:
                        attribute_access_result = BoundMethod(
                            runtime_term,
                            unwrapped_runtime_functions_to_named_function_definitions[unwrapped_attribute]
                        )
                    else:
                        attribute_access_result = BoundMethod(
                            runtime_term,
                            unwrapped_attribute
                        )
        else:
            logging.error('Cannot access attribute `%s` in class %s!', attribute_name, runtime_term.class_)

    return attribute_access_result
