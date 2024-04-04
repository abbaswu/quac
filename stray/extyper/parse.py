from typing import Union, Optional

from extyper.errors import Errors
from extyper.options import Options
from extyper.nodes import MypyFile


def parse(source: Union[str, bytes],
          fnam: str,
          module: Optional[str],
          errors: Optional[Errors],
          options: Options) -> MypyFile:
    """Parse a source file, without doing any semantic analysis.

    Return the parse tree. If errors is not provided, raise ParseError
    on failure. Otherwise, use the errors object to report parse errors.

    The python_version (major, minor) option determines the Python syntax variant.
    """
    is_stub_file = fnam.endswith('.pyi')
    if options.transform_source is not None:
        source = options.transform_source(source)
    if options.python_version[0] >= 3 or is_stub_file:
        import extyper.fastparse
        return extyper.fastparse.parse(source,
                                    fnam=fnam,
                                    module=module,
                                    errors=errors,
                                    options=options)
    else:
        import extyper.fastparse2
        return extyper.fastparse2.parse(source,
                                     fnam=fnam,
                                     module=module,
                                     errors=errors,
                                     options=options)
