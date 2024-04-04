import typing
import logging

from collections import defaultdict

from type_definitions import *


def get_module_names_to_imported_names_to_runtime_objects(
        module_names_to_import_tuple_sets: typing.Mapping[str, typing.Set[tuple[str, str]]],
        module_names_to_import_from_tuple_sets: typing.Mapping[str, typing.Set[tuple[str, str, str]]],
        module_names_to_modules: typing.Mapping[str, Module]
):
    """
    Map top-level imported names to runtime objects.
    Import tuple sets and import from tuple sets come from running `do_static_import_analysis` on the project.
    An import tuple is a 2-tuple: (imported_module_name, imported_module_name_alias).
    An import from tuple is a 3-tuple: (import_from_module_name, imported_name, imported_name_alias).
    The mapping from module names to modules come from obtaining `sys.modules` after importing the project's modules.
    """
    module_names_to_imported_names_to_runtime_objects: defaultdict[str, dict[str, object]] = defaultdict(dict)

    for module_name, import_tuple_set in module_names_to_import_tuple_sets.items():
        if module_name in module_names_to_modules:
            module = module_names_to_modules[module_name]
            imported_names_to_runtime_objects = module_names_to_imported_names_to_runtime_objects.setdefault(module_name, {})

            for (imported_module_name, imported_module_name_alias) in import_tuple_set:
                # Only the first component of the imported_module_name_alias is an imported name
                imported_module_name_alias_components = imported_module_name_alias.split('.')
                imported_name_alias = imported_module_name_alias_components[0]

                if imported_name_alias in module.__dict__:
                    runtime_object = module.__dict__[imported_name_alias]

                    imported_names_to_runtime_objects[imported_name_alias] = runtime_object
                    logging.info('Matched imported name %s in module %s to the runtime object %s', imported_name_alias,
                                 module_name, runtime_object)
                else:
                    logging.error('Cannot match imported name %s in module %s to a runtime object!',
                                  imported_name_alias, module_name)
        else:
            logging.error('Cannot match module %s to a runtime module!', module_name)

    for module_name, import_from_tuple_set in module_names_to_import_from_tuple_sets.items():
        if module_name in module_names_to_modules:
            module = module_names_to_modules[module_name]
            imported_names_to_runtime_objects = module_names_to_imported_names_to_runtime_objects.setdefault(module_name, {})

            for (import_from_module_name, imported_name, imported_name_alias) in import_from_tuple_set:
                # Special handling when imported_name_alias == '*'
                if imported_name_alias == '*':
                    # Try to retrieve import_from_module
                    if import_from_module_name in module_names_to_modules:
                        import_from_module = module_names_to_modules[import_from_module_name]

                        # The public names defined by a module are determined by checking the module's namespace for a variable named __all__;
                        # if defined, it must be a sequence of strings which are names defined or imported by that module.
                        # The names given in __all__ are all considered public and are required to exist.
                        # If __all__ is not defined, the set of public names includes all names found in the module's namespace which do not begin with an underscore character ('_')
                        if '__all__' in import_from_module.__dict__:
                            for name in import_from_module.__dict__['__all__']:
                                imported_names_to_runtime_objects[name] = import_from_module.__dict__[name]
                        else:
                            for name, value in import_from_module.__dict__.items():
                                if not name.startswith('_'):
                                    imported_names_to_runtime_objects[name] = value
                        logging.info('Handled `from %s import *` in module %s', import_from_module_name, module_name)
                    else:
                        logging.error(
                            'Cannot match module %s to a runtime module, thus cannot handle `from %s import *` in module %s!',
                            import_from_module_name, import_from_module_name, module_name)
                else:
                    if imported_name_alias in module.__dict__:
                        runtime_object = module.__dict__[imported_name_alias]

                        imported_names_to_runtime_objects[imported_name_alias] = runtime_object
                        logging.info('Matched imported name %s in module %s to the runtime object %s',
                                     imported_name_alias, module_name, runtime_object)
                    else:
                        logging.error('Cannot match imported name %s in module %s to a runtime object!',
                                      imported_name_alias, module_name)
        else:
            logging.error('Cannot match module %s to a runtime module!', module_name)

    return module_names_to_imported_names_to_runtime_objects
