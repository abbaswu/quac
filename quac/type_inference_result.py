from typing import Generator, Optional


class TypeInferenceClass:
    __slots__ = ('module_name', 'class_name')

    def __init__(self, module_name: Optional[str], name: str):
        self.module_name = module_name
        self.class_name = name

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeInferenceClass):
            return self.module_name == other.module_name and self.class_name == other.class_name
        return False

    def __hash__(self) -> int:
        return hash((self.module_name, self.class_name))

    def string_representation_in_module(self, module_name: Optional[str]) -> str:
        # Special representations for builtins.NoneType and builtins.ellipsis
        if self.module_name == 'builtins':
            if self.class_name == 'NoneType':
                return 'None'
            elif self.class_name == 'ellipsis':
                return '...'
        if self.module_name and self.module_name != module_name:
            return f'{self.module_name}.{self.class_name}'
        else:
            return self.class_name

    def __repr__(self) -> str:
        return self.string_representation_in_module(None)


class TypeInferenceResult:
    __slots__ = ('type_inference_class', 'filled_type_variables')

    def __init__(self, type_inference_class: TypeInferenceClass, filled_type_variables: tuple['TypeInferenceResult', ...] = ()):
        self.type_inference_class = type_inference_class
        self.filled_type_variables = filled_type_variables

    def __eq__(self, other: object) -> bool:
        if isinstance(other, TypeInferenceResult):
            return (
                self.type_inference_class == other.type_inference_class
                and self.filled_type_variables == other.filled_type_variables
            )
        return False

    def __hash__(self) -> int:
        return hash((self.type_inference_class, self.filled_type_variables))

    def string_representation_in_module(self, module_name: Optional[str]) -> str:
        components: list[str] = [self.type_inference_class.string_representation_in_module(module_name)]

        if self.filled_type_variables:
            filled_type_variable_components: list[str] = [
                filled_type_variable.string_representation_in_module(module_name)
                for filled_type_variable in self.filled_type_variables
            ]

            components.append('[')

            # Special handling for typing.Callable and collections.abc.Callable
            if self.type_inference_class in (
                TypeInferenceClass('typing', 'Callable'),
                TypeInferenceClass('collections.abc', 'Callable')
            ):
                # Situation 1: len(filled_type_variable_components) == 1
                # Add '[]' representing empty parameter list in addition to filled_type_variable_components[0]
                if len(filled_type_variable_components) == 1:
                    components.append('[]')
                    components.append(', ')
                    components.append(filled_type_variable_components[0])
                # Situation 2: len(filled_type_variable_components) == 2 and self.filled_type_variables[0].type_inference_class == TypeInferenceClass('builtins', 'ellipsis')
                # Directly extend with filled_type_variable_components
                elif len(filled_type_variable_components) == 2 and self.filled_type_variables[0].type_inference_class == TypeInferenceClass('builtins', 'ellipsis'):
                    components.append(', '.join(filled_type_variable_components))
                # Situation 3: Other situations where len(filled_type_variable_components) > 1
                # Add '[' and ']' at the start and end of the parameter list
                elif len(filled_type_variable_components) > 1:
                    components.append('[')
                    components.append(', '.join(filled_type_variable_components[:-1]))
                    components.append(']')
                    components.append(', ')
                    components.append(filled_type_variable_components[-1])
            else:
                components.append(', '.join(filled_type_variable_components))
            
            components.append(']')

        return ''.join(components)

    def __repr__(self) -> str:
        return self.string_representation_in_module(None)


def iterate_type_inference_classes(type_inference_result: TypeInferenceResult) -> Generator[
    TypeInferenceClass,
    None,
    None
]:
    yield type_inference_result.type_inference_class
    for filled_type_variable in type_inference_result.filled_type_variables:
        yield from iterate_type_inference_classes(filled_type_variable)

