import ast

from .get_imports_and_raw_import_froms_in_ast_module import get_imports_and_raw_import_froms_in_ast_module


# Returns a `tuple[set[tuple[str, str]], set[tuple[str, str, str]]]`
# The first `set[tuple[str, str]]` contains `Import`'s represented as 2-tuples: (module_name, module_name_alias)
# The second `set[tuple[str, str, str]]]` contains `ImportFrom`'s represented as 3-tuples: (module_name, imported_name, imported_name_alias)
# References: 
# https://docs.python.org/3/library/ast.html#ast.ClassDef
def get_imports_and_import_froms_in_ast_module(ast_module: ast.Module, module_name: str, is_package: bool = False) -> tuple[set[tuple[str, str]], set[tuple[str, str, str]]]:
    module_name_components = module_name.split('.')

    imports, raw_import_froms = get_imports_and_raw_import_froms_in_ast_module(ast_module)

    import_froms: set[tuple[str, str, str]] = set()
    for raw_module_name, module_level, imported_name, imported_name_alias in raw_import_froms:
        if module_level:
            if is_package:
                module_name = '.'.join(
                    # drop `module_level - 1` components from the back of `module_name_components`
                    # this is because `module_level` is relative to `__init__.py` within the package
                    # not the package itself
                    module_name_components[:(len(module_name_components) - (module_level - 1))]
                )
            else:
                module_name = '.'.join(
                    # drop `module_level` components from the back of `module_name_components`
                    module_name_components[:(len(module_name_components) - module_level)]
                )

            if raw_module_name is not None:
                module_name += '.' + raw_module_name
        else:
            assert raw_module_name is not None
            module_name = raw_module_name

        import_froms.add((module_name, imported_name, imported_name_alias))

    return imports, import_froms
