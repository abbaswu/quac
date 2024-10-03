import ast
import collections.abc
import logging
import typing

from extract_single_non_none_typeshed_class import extract_single_non_none_typeshed_class
from get_attributes_in_runtime_class import get_attributes_in_runtime_class
from get_attributes_in_typeshed_class_definition import get_attributes_in_typeshed_class_definition
from get_comprehensive_dict_for_runtime_class import get_comprehensive_dict_for_runtime_class
from get_unwrapped_constructor import get_unwrapped_constructor
from type_definitions import (
    RuntimeTerm,
    Module,
    RuntimeClass,
    Function,
    Instance,
    UnwrappedRuntimeFunction,
    FunctionDefinition,
    UnboundMethod,
    BoundMethod
)
from typeshed_client_ex.client import Client
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
from unwrap import unwrap


def handle_matching_parameter_with_argument(
        parameter: ast.AST,
        argument: ast.AST,
        add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    add_subset_callback(
        argument, # superset
        parameter # subset
    )


def handle_matching_return_value_with_returned_value(
        return_value: ast.AST,
        returned_value: ast.AST,
        add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    add_subset_callback(
        returned_value, # superset
        return_value # subset
    )


def handle_user_defined_function(
        function_definition: FunctionDefinition,
        function_definitions_to_parameters_name_parameter_mappings_and_return_values: typing.Mapping[
            FunctionDefinition,
            tuple[
                typing.Sequence[ast.AST],
                typing.Mapping[str, ast.AST],
                ast.AST]
        ],
        apparent_arguments: typing.Sequence[ast.AST],
        names_to_arguments: typing.Mapping[str, ast.AST],
        returned_value: ast.AST,
        skip_first_parameter: bool,
        skip_return_value: bool,
        add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    if function_definition in function_definitions_to_parameters_name_parameter_mappings_and_return_values:
        (
            parameters,
            names_to_parameters,
            return_value
        ) = function_definitions_to_parameters_name_parameter_mappings_and_return_values.get(
            function_definition
        )

        if skip_first_parameter:
            used_parameters = parameters[1:]
        else:
            used_parameters = parameters
        
        # Handle parameter propagation.
        for parameter, argument in zip(used_parameters, apparent_arguments):
            handle_matching_parameter_with_argument(
                parameter,
                argument,
                add_subset_callback
            )

        for name in names_to_parameters.keys() & names_to_arguments.keys():
            parameter = names_to_parameters[name]
            argument = names_to_arguments[name]
            handle_matching_parameter_with_argument(
                parameter,
                argument,
                add_subset_callback
            )

        # Handle return value propagation.
        if not skip_return_value:
            handle_matching_return_value_with_returned_value(
                return_value,
                returned_value,
                add_subset_callback
            )


def handle_isinstance(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # isinstance(object, classinfo)
    # Only support classinfo being literal classes and literal tuples containing literal classes.
    runtime_classes: set[RuntimeClass]
    
    object_node = apparent_arguments[0]
    classinfo_node = apparent_arguments[1]

    if isinstance(classinfo_node, ast.Tuple):
        runtime_classes = {
            runtime_term
            for elt in classinfo_node.elts
            if not isinstance(elt, ast.Starred)
            for runtime_term in get_runtime_terms_callback(elt)
            if isinstance(runtime_term, RuntimeClass)
        }
    else:
        runtime_classes = {
            runtime_term
            for runtime_term in get_runtime_terms_callback(classinfo_node)
            if isinstance(runtime_term, RuntimeClass)
        }
    
    attributes = set().union(
        *(get_attributes_in_runtime_class(runtime_class) for runtime_class in runtime_classes)
    )

    update_runtime_terms_callback(object_node, runtime_classes)
    update_bag_of_attributes_callback(object_node, attributes)

    update_runtime_terms_callback(returned_value, {Instance(bool)})
    update_bag_of_attributes_callback(returned_value, get_attributes_in_runtime_class(bool))


def handle_attr_common(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # ...(object, name)
    # Update the bag of attributes of `object`.
    # Only support name being literal strings.
    attribute_names: set[str] = set()

    object_node = apparent_arguments[0]
    name_node = apparent_arguments[1]

    if isinstance(name_node, ast.Constant) and isinstance(name_node.value, str):
        attribute_names.add(name_node.value)
    
    update_bag_of_attributes_callback(object_node, attribute_names)


def handle_delattr(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # delattr(object, name)
    # Update the bag of attributes of `object`.
    # Only support name being literal strings.
    handle_attr_common(
        apparent_arguments,
        names_to_arguments,
        returned_value,
        skip_first_parameter,
        skip_return_value,
        get_runtime_terms_callback,
        update_runtime_terms_callback,
        update_bag_of_attributes_callback,
        add_subset_callback
    )


def handle_getattr(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # getattr(object, name)
    # getattr(object, name, default)
    # Update the bag of attributes of `object`.
    # Only support name being literal strings.
    handle_attr_common(
        apparent_arguments,
        names_to_arguments,
        returned_value,
        skip_first_parameter,
        skip_return_value,
        get_runtime_terms_callback,
        update_runtime_terms_callback,
        update_bag_of_attributes_callback,
        add_subset_callback
    )

    if len(apparent_arguments) == 3:
        default_node = apparent_arguments[2]
        add_subset_callback(
            returned_value, # superset
            default_node, # subset
        )


def handle_hasattr(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # hasattr(object, name)
    # Update the bag of attributes of `object`.
    # Only support name being literal strings.
    handle_attr_common(
        apparent_arguments,
        names_to_arguments,
        returned_value,
        skip_first_parameter,
        skip_return_value,
        get_runtime_terms_callback,
        update_runtime_terms_callback,
        update_bag_of_attributes_callback,
        add_subset_callback
    )

    update_runtime_terms_callback(returned_value, {Instance(bool)})
    update_bag_of_attributes_callback(returned_value, get_attributes_in_runtime_class(bool))


def handle_setattr(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # setattr(object, name, value)
    # Update the bag of attributes of `object`.
    # Only support name being literal strings.
    handle_attr_common(
        apparent_arguments,
        names_to_arguments,
        returned_value,
        skip_first_parameter,
        skip_return_value,
        get_runtime_terms_callback,
        update_runtime_terms_callback,
        update_bag_of_attributes_callback,
        add_subset_callback
    )


def handle_open(
    apparent_arguments: typing.Sequence[ast.AST],
    names_to_arguments: typing.Mapping[str, ast.AST],
    returned_value: ast.AST,
    skip_first_parameter: bool,
    skip_return_value: bool,
    get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
):
    # open(file, mode='r', buffering=-1, encoding=None, errors=None, newline=None, closefd=True, opener=None)
    # Open file and return a corresponding file object.
    # file is a path-like object giving the pathname.
    # mode is an optional string that specifies the mode in which the file is opened.
    # buffering is an optional integer used to set the buffering policy.
    # encoding is the name of the encoding used to decode or encode the file.
    # errors is an optional string that specifies how encoding and decoding errors are to be handled.
    # newline determines how to parse newline characters from the stream.
    # A custom opener can be used by passing a callable as opener.
    for (argument, (runtime_terms, attribute_set)) in zip(
        apparent_arguments,
        [
            ({Instance(str)}, get_attributes_in_runtime_class(str)), # file
            ({Instance(str)}, get_attributes_in_runtime_class(str)), # mode
            ({Instance(int)}, get_attributes_in_runtime_class(int)), # buffering
            ({Instance(str)}, get_attributes_in_runtime_class(str)), # encoding
            ({Instance(str)}, get_attributes_in_runtime_class(str)), # errors
            ({Instance(str)}, get_attributes_in_runtime_class(str)), # newline
            ({Instance(bool)}, get_attributes_in_runtime_class(bool)), # closefd
            ({Instance(collections.abc.Callable)}, get_attributes_in_runtime_class(collections.abc.Callable)), # opener
        ]
    ):
        update_runtime_terms_callback(argument, runtime_terms)
        update_bag_of_attributes_callback(argument, attribute_set)
    
    update_runtime_terms_callback(returned_value, {Instance(typing.IO)})
    update_bag_of_attributes_callback(returned_value, get_attributes_in_runtime_class(typing.IO))


SPECIAL_EXTERNAL_FUNCTIONS_TO_HANDLERS = {
    ('builtins', 'global', 'isinstance'): handle_isinstance,
    ('builtins', 'global', 'delattr'): handle_delattr,
    ('builtins', 'global', 'getattr'): handle_getattr,
    ('builtins', 'global', 'hasattr'): handle_hasattr,
    ('builtins', 'global', 'setattr'): handle_setattr,
    ('io', 'global', 'open'): handle_open,
}


def ascribe_typeshed_class(
    node: ast.AST,
    typeshed_class: TypeshedClass,
    update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
    update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
    typeshed_client: Client,
):
    runtime_class: typing.Optional[RuntimeClass]
    attribute_set: set[str]
    
    runtime_class = to_runtime_class(typeshed_class)
    if runtime_class is not None:
        attribute_set = get_attributes_in_runtime_class(runtime_class)
    else:
        try:
            typeshed_class_definition = typeshed_client.get_class_definition(typeshed_class)
            attribute_set = get_attributes_in_typeshed_class_definition(typeshed_class_definition)
        except (ModuleNotFoundError, KeyError, AttributeError):
            logging.exception('Cannot retrieve Typeshed class definition for %s!', typeshed_class)
            attribute_set = set()
    
    if runtime_class is not None:
        update_runtime_terms_callback(node, {Instance(runtime_class)})
    
    if attribute_set:
        update_bag_of_attributes_callback(node, attribute_set)


def handle_external_function(
        module_name: str,
        class_name_or_global: str,
        function_name: str,
        apparent_arguments: typing.Sequence[ast.AST],
        names_to_arguments: typing.Mapping[str, ast.AST],
        returned_value: ast.AST,
        skip_first_parameter: bool,
        skip_return_value: bool,
        get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
        update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
        update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
        add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
        typeshed_client: Client,
):
    global SPECIAL_EXTERNAL_FUNCTIONS_TO_HANDLERS

    if (module_name, class_name_or_global, function_name) in SPECIAL_EXTERNAL_FUNCTIONS_TO_HANDLERS:
        return SPECIAL_EXTERNAL_FUNCTIONS_TO_HANDLERS[(module_name, class_name_or_global, function_name)](
            apparent_arguments,
            names_to_arguments,
            returned_value,
            skip_first_parameter,
            skip_return_value,
            get_runtime_terms_callback,
            update_runtime_terms_callback,
            update_bag_of_attributes_callback,
            add_subset_callback,
        )
    else:
        try:
            # Global function
            if class_name_or_global == 'global':
                typeshed_function_definition_list = typeshed_client.get_function_definition(
                    typeshed_client.look_up_name(module_name, function_name)
                )
            # Method
            else:
                typeshed_function_definition_list = typeshed_client.get_class_definition(
                    typeshed_client.look_up_name(module_name, class_name_or_global)
                ).method_name_to_method_list_dict[function_name]

            (
                parameter_type_annotations,
                return_value_type_annotation
            ) = get_comprehensive_type_annotations_for_parameters_and_return_values(
                typeshed_function_definition_list
            )

            if skip_first_parameter:
                used_parameter_type_annotations = parameter_type_annotations[1:]
            else:
                used_parameter_type_annotations = parameter_type_annotations

            # Invoke Typeshed class ascription procedure on apparent arguments and return values.
            for argument, parameter_type_annotation in zip(
                    apparent_arguments,
                    used_parameter_type_annotations
            ):
                if (
                    single_non_none_parameter_typeshed_class := extract_single_non_none_typeshed_class(
                        parameter_type_annotation
                    ) 
                ) is not None:
                    ascribe_typeshed_class(
                        argument,
                        single_non_none_parameter_typeshed_class,
                        update_runtime_terms_callback,
                        update_bag_of_attributes_callback,
                        typeshed_client,
                    )
            
            if not skip_return_value:
                if (
                    single_non_none_return_value_typeshed_class := extract_single_non_none_typeshed_class(
                        return_value_type_annotation
                    ) 
                ) is not None:
                    ascribe_typeshed_class(
                        returned_value,
                        single_non_none_return_value_typeshed_class,
                        update_runtime_terms_callback,
                        update_bag_of_attributes_callback,
                        typeshed_client,
                    )
            
        except (ModuleNotFoundError, KeyError, AttributeError):
            logging.error(
                'Failed to retrieve Typeshed stubs for external function %s :: %s :: %s!',
                module_name,
                class_name_or_global,
                function_name
            )

def handle_function_call(
        runtime_term: RuntimeTerm,
        apparent_arguments: typing.Sequence[ast.AST],
        names_to_arguments: typing.Mapping[str, ast.AST],
        returned_value: ast.AST,
        unwrapped_runtime_functions_to_named_function_definitions: typing.Mapping[UnwrappedRuntimeFunction, FunctionDefinition],
        function_definitions_to_parameters_name_parameter_mappings_and_return_values: typing.Mapping[
            FunctionDefinition,
            tuple[
                typing.Sequence[ast.AST],
                typing.Mapping[str, ast.AST],
                ast.AST]
        ],
        get_runtime_terms_callback: typing.Callable[[ast.AST], typing.Iterable[RuntimeTerm]],
        update_runtime_terms_callback: typing.Callable[[ast.AST, typing.Iterable[RuntimeTerm]], typing.Any],
        update_bag_of_attributes_callback: typing.Callable[[ast.AST, typing.Iterable[str]], typing.Any],
        add_subset_callback: typing.Callable[[ast.AST, ast.AST], typing.Any],
        typeshed_client: Client,
):
    def partially_applied_handle_user_defined_function(
        function_definition: FunctionDefinition,
        skip_first_parameter: bool,
        skip_return_value: bool
    ):
        return handle_user_defined_function(
            function_definition,
            function_definitions_to_parameters_name_parameter_mappings_and_return_values,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            skip_first_parameter,
            skip_return_value,
            add_subset_callback,
        )
    
    def partially_applied_handle_external_function(
        module_name: str,
        class_name_or_global: str,
        function_name: str,
        skip_first_parameter: bool,
        skip_return_value: bool
    ):
        return handle_external_function(
            module_name,
            class_name_or_global,
            function_name,
            apparent_arguments,
            names_to_arguments,
            returned_value,
            skip_first_parameter,
            skip_return_value,
            get_runtime_terms_callback,
            update_runtime_terms_callback,
            update_bag_of_attributes_callback,
            add_subset_callback,
            typeshed_client,
        )
    
    skip_first_parameter: bool
    skip_return_value: bool

    if isinstance(runtime_term, RuntimeClass):
        skip_first_parameter = True
        skip_return_value = True

        # Get the RuntimeClass's constructor
        unwrapped_constructor = get_unwrapped_constructor(runtime_term)

        if unwrapped_constructor in unwrapped_runtime_functions_to_named_function_definitions:
            partially_applied_handle_user_defined_function(
                unwrapped_runtime_functions_to_named_function_definitions[unwrapped_constructor],
                skip_first_parameter,
                skip_return_value,
            )
        else:
            partially_applied_handle_external_function(
                runtime_term.__module__,
                runtime_term.__name__,
                unwrapped_constructor.__name__,
                skip_first_parameter,
                skip_return_value,
            )
        
        # Associate the returned value with an instance of the class
        update_runtime_terms_callback(returned_value, {Instance(runtime_term)})
        update_bag_of_attributes_callback(returned_value, get_attributes_in_runtime_class(runtime_term))
    elif isinstance(runtime_term, Function):
        skip_first_parameter = False
        skip_return_value = False

        if isinstance(runtime_term, FunctionDefinition):
            partially_applied_handle_user_defined_function(
                runtime_term,
                skip_first_parameter,
                skip_return_value,
            )
        elif isinstance(runtime_term, UnwrappedRuntimeFunction):
            partially_applied_handle_external_function(
                runtime_term.__module__,
                'global',
                runtime_term.__name__,
                skip_first_parameter,
                skip_return_value,
            )
        else:
            logging.error('Cannot handle calling function %s!', runtime_term)
    elif isinstance(runtime_term, UnboundMethod):
        skip_first_parameter = False
        skip_return_value = False

        # Extract the function
        function = runtime_term.function

        if isinstance(function, FunctionDefinition):
            partially_applied_handle_user_defined_function(
                function,
                skip_first_parameter,
                skip_return_value,
            )
        elif isinstance(function, UnwrappedRuntimeFunction):
            partially_applied_handle_external_function(
                runtime_term.class_.__module__,
                runtime_term.class_.__name__,
                function.__name__,
                skip_first_parameter,
                skip_return_value,
            )
        else:
            logging.error('Cannot handle calling unbound method %s!', runtime_term)
    elif isinstance(runtime_term, Instance):
        skip_first_parameter = True
        skip_return_value = False

        runtime_term_class_dict = get_comprehensive_dict_for_runtime_class(runtime_term.class_)
        if '__call__' in runtime_term_class_dict:
            unwrapped_call = unwrap(runtime_term_class_dict['__call__'])

            if unwrapped_call in unwrapped_runtime_functions_to_named_function_definitions:
                partially_applied_handle_user_defined_function(
                    unwrapped_runtime_functions_to_named_function_definitions[unwrapped_call],
                    skip_first_parameter,
                    skip_return_value,
                )
            else:
                partially_applied_handle_external_function(
                    runtime_term.class_.__module__,
                    runtime_term.class_.__name__,
                    unwrapped_call.__name__,
                    skip_first_parameter,
                    skip_return_value,
                )
        else:
            logging.error('Cannot handle calling instance %s - it does not provide the `__call__` method!', runtime_term)
    elif isinstance(runtime_term, BoundMethod):
        skip_first_parameter = True
        skip_return_value = False

        # Extract the function
        function = runtime_term.function
        
        if isinstance(function, FunctionDefinition):
            partially_applied_handle_user_defined_function(
                function,
                skip_first_parameter,
                skip_return_value,
            )
        elif isinstance(function, UnwrappedRuntimeFunction):
            partially_applied_handle_external_function(
                runtime_term.instance.class_.__module__,
                runtime_term.instance.class_.__name__,
                function.__name__,
                skip_first_parameter,
                skip_return_value,
            )
        else:
            logging.error('Cannot handle calling bound method %s!', runtime_term)
    else:
        logging.error('Cannot handle calling unknown runtime term %s!', runtime_term)
