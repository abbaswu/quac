"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=parse_stray_type_annotations test_parse_stray_type_annotations.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""

from type_inference_result import TypeInferenceResult
from parse_stray_type_annotations import parser, handle_type_annotation_tree


def parse(
    type_annotation_string: str
) -> TypeInferenceResult:
    type_annotation_tree: Tree = parser.parse(type_annotation_string)
    return handle_type_annotation_tree(
        type_annotation_tree,
        dict()
    )


if __name__ == '__main__':
    import io
    import builtins
    import typing
    import os

    assert str(parse('None')) == 'None'
    assert str(parse('builtins.int')) == 'builtins.int'
    assert str(parse('Tuple[Any, def (*args: Any, **kw: Any) -> ctypes.Structure]')) == 'builtins.tuple[typing.Any, typing.Callable[..., ctypes.Structure]]'
    assert str(parse('Any')) == 'typing.Any'
    assert str(parse('Tuple[builtins.int, builtins.int, builtins.int]')) == 'builtins.tuple[builtins.int, builtins.int, builtins.int]'
    assert str(parse('builtins.tuple[builtins.int]')) == 'builtins.tuple[builtins.int, ...]'
    assert str(parse('<nothing>')) == 'typing.NoReturn'
    assert str(parse('Tuple[<partial None>, <partial None>]')) == 'builtins.tuple[None, None]'
    assert str(parse('Tuple[Union[Any, builtins.str], Union[Any, builtins.str]]')) == 'builtins.tuple[typing.Union[typing.Any, builtins.str], typing.Union[typing.Any, builtins.str]]'
    assert str(parse('Tuple[<partial list[?]>, builtins.list[builtins.tuple[builtins.str]]]')) == 'builtins.tuple[builtins.list[typing.Any], builtins.list[builtins.tuple[builtins.str, ...]]]'
    assert str(parse('grpc_status.rpc_status._Status@9')) == 'grpc_status.rpc_status._Status'

    assert eval(str(parse('def (max_workers: Union[None, builtins.int] =, thread_name_prefix: builtins.str =, initializer: Union[None, def (*Any, **Any)] =, initargs: builtins.tuple[Any] =) -> builtins.int'))) == typing.Callable[[typing.Union[None, builtins.int], builtins.str, typing.Union[None, typing.Callable[..., None]], builtins.tuple[typing.Any, ...]], builtins.int]
    
    assert eval(str(parse('Tuple[]'))) == builtins.tuple

    assert eval(str(parse("Literal['+a']"))) == typing.Literal['+a']

    assert eval(str(parse(
        "def (s: Union[builtins.bytes, builtins.str], *, cls: Union[None, Type[json.decoder.JSONDecoder]] =, object_hook: Union[None, def (builtins.dict[Any, Any]) -> Any] =, parse_float: Union[None, def (builtins.str) -> Any] =, parse_int: Union[None, def (builtins.str) -> Any] =, parse_constant: Union[None, def (builtins.str) -> Any] =, object_pairs_hook: Union[None, def (builtins.list[Tuple[Any, Any]]) -> Any] =, **kwds: Any) -> Any"
    ))) == typing.Callable[..., typing.Any]
    
    assert eval(str(parse(
        "Overload(def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['+a'], Literal['+at'], Literal['+r'], Literal['+rt'], Literal['+ta'], Literal['+tr'], Literal['+tw'], Literal['+tx'], Literal['+w'], Literal['+wt'], Literal['+x'], Literal['+xt'], Literal['U'], Literal['Ur'], Literal['Urt'], Literal['Utr'], Literal['a'], Literal['a+'], Literal['a+t'], Literal['at'], Literal['at+'], Literal['r'], Literal['r+'], Literal['r+t'], Literal['rU'], Literal['rUt'], Literal['rt'], Literal['rt+'], Literal['rtU'], Literal['t+a'], Literal['t+r'], Literal['t+w'], Literal['t+x'], Literal['tUr'], Literal['ta'], Literal['ta+'], Literal['tr'], Literal['tr+'], Literal['trU'], Literal['tw'], Literal['tw+'], Literal['tx'], Literal['tx+'], Literal['w'], Literal['w+'], Literal['w+t'], Literal['wt'], Literal['wt+'], Literal['x'], Literal['x+'], Literal['x+t'], Literal['xt'], Literal['xt+']] =, buffering: builtins.int =, encoding: Union[None, builtins.str] =, errors: Union[None, builtins.str] =, newline: Union[None, builtins.str] =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> io.TextIOWrapper, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['+ab'], Literal['+ba'], Literal['+br'], Literal['+bw'], Literal['+bx'], Literal['+rb'], Literal['+wb'], Literal['+xb'], Literal['Ubr'], Literal['Urb'], Literal['a+b'], Literal['ab'], Literal['ab+'], Literal['b+a'], Literal['b+r'], Literal['b+w'], Literal['b+x'], Literal['bUr'], Literal['ba'], Literal['ba+'], Literal['br'], Literal['br+'], Literal['brU'], Literal['bw'], Literal['bw+'], Literal['bx'], Literal['bx+'], Literal['r+b'], Literal['rUb'], Literal['rb'], Literal['rb+'], Literal['rbU'], Literal['w+b'], Literal['wb'], Literal['wb+'], Literal['x+b'], Literal['xb'], Literal['xb+']], buffering: Literal[0], encoding: None =, errors: None =, newline: None =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> io.FileIO, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['+ab'], Literal['+ba'], Literal['+br'], Literal['+bw'], Literal['+bx'], Literal['+rb'], Literal['+wb'], Literal['+xb'], Literal['a+b'], Literal['ab+'], Literal['b+a'], Literal['b+r'], Literal['b+w'], Literal['b+x'], Literal['ba+'], Literal['br+'], Literal['bw+'], Literal['bx+'], Literal['r+b'], Literal['rb+'], Literal['w+b'], Literal['wb+'], Literal['x+b'], Literal['xb+']], buffering: Union[Literal[-1], Literal[1]] =, encoding: None =, errors: None =, newline: None =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> io.BufferedRandom, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['ab'], Literal['ba'], Literal['bw'], Literal['bx'], Literal['wb'], Literal['xb']], buffering: Union[Literal[-1], Literal[1]] =, encoding: None =, errors: None =, newline: None =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> io.BufferedWriter, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['Ubr'], Literal['Urb'], Literal['bUr'], Literal['br'], Literal['brU'], Literal['rUb'], Literal['rb'], Literal['rbU']], buffering: Union[Literal[-1], Literal[1]] =, encoding: None =, errors: None =, newline: None =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> io.BufferedReader, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: Union[Literal['+ab'], Literal['+ba'], Literal['+br'], Literal['+bw'], Literal['+bx'], Literal['+rb'], Literal['+wb'], Literal['+xb'], Literal['Ubr'], Literal['Urb'], Literal['a+b'], Literal['ab'], Literal['ab+'], Literal['b+a'], Literal['b+r'], Literal['b+w'], Literal['b+x'], Literal['bUr'], Literal['ba'], Literal['ba+'], Literal['br'], Literal['br+'], Literal['brU'], Literal['bw'], Literal['bw+'], Literal['bx'], Literal['bx+'], Literal['r+b'], Literal['rUb'], Literal['rb'], Literal['rb+'], Literal['rbU'], Literal['w+b'], Literal['wb'], Literal['wb+'], Literal['x+b'], Literal['xb'], Literal['xb+']], buffering: builtins.int, encoding: None =, errors: None =, newline: None =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> typing.BinaryIO, def (file: Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], mode: builtins.str, buffering: builtins.int =, encoding: Union[None, builtins.str] =, errors: Union[None, builtins.str] =, newline: Union[None, builtins.str] =, closefd: builtins.bool =, opener: Union[None, def (builtins.str, builtins.int) -> builtins.int] =) -> typing.IO[Any])"
    ))) == typing.Callable[[typing.Union[builtins.bytes, builtins.int, builtins.str, os.PathLike[builtins.bytes], os.PathLike[builtins.str]], typing.Union[typing.Literal['Ubr'], typing.Literal['Urb'], typing.Literal['bUr'], typing.Literal['br'], typing.Literal['brU'], typing.Literal['rUb'], typing.Literal['rb'], typing.Literal['rbU'], typing.Literal['+ab'], typing.Literal['+ba'], typing.Literal['+br'], typing.Literal['+bw'], typing.Literal['+bx'], typing.Literal['+rb'], typing.Literal['+wb'], typing.Literal['+xb'], typing.Literal['a+b'], typing.Literal['ab'], typing.Literal['ab+'], typing.Literal['b+a'], typing.Literal['b+r'], typing.Literal['b+w'], typing.Literal['b+x'], typing.Literal['ba'], typing.Literal['ba+'], typing.Literal['br+'], typing.Literal['bw'], typing.Literal['bw+'], typing.Literal['bx'], typing.Literal['bx+'], typing.Literal['r+b'], typing.Literal['rb+'], typing.Literal['w+b'], typing.Literal['wb'], typing.Literal['wb+'], typing.Literal['x+b'], typing.Literal['xb'], typing.Literal['xb+'], builtins.str, typing.Literal['+a'], typing.Literal['+at'], typing.Literal['+r'], typing.Literal['+rt'], typing.Literal['+ta'], typing.Literal['+tr'], typing.Literal['+tw'], typing.Literal['+tx'], typing.Literal['+w'], typing.Literal['+wt'], typing.Literal['+x'], typing.Literal['+xt'], typing.Literal['U'], typing.Literal['Ur'], typing.Literal['Urt'], typing.Literal['Utr'], typing.Literal['a'], typing.Literal['a+'], typing.Literal['a+t'], typing.Literal['at'], typing.Literal['at+'], typing.Literal['r'], typing.Literal['r+'], typing.Literal['r+t'], typing.Literal['rU'], typing.Literal['rUt'], typing.Literal['rt'], typing.Literal['rt+'], typing.Literal['rtU'], typing.Literal['t+a'], typing.Literal['t+r'], typing.Literal['t+w'], typing.Literal['t+x'], typing.Literal['tUr'], typing.Literal['ta'], typing.Literal['ta+'], typing.Literal['tr'], typing.Literal['tr+'], typing.Literal['trU'], typing.Literal['tw'], typing.Literal['tw+'], typing.Literal['tx'], typing.Literal['tx+'], typing.Literal['w'], typing.Literal['w+'], typing.Literal['w+t'], typing.Literal['wt'], typing.Literal['wt+'], typing.Literal['x'], typing.Literal['x+'], typing.Literal['x+t'], typing.Literal['xt'], typing.Literal['xt+']], typing.Union[builtins.int, typing.Literal[-1], typing.Literal[1], typing.Literal[0]], typing.Union[None, builtins.str], typing.Union[None, builtins.str], typing.Union[None, builtins.str], builtins.bool, typing.Union[None, typing.Callable[[builtins.str, builtins.int], builtins.int]]], typing.Union[io.BufferedRandom, io.FileIO, typing.BinaryIO, io.BufferedReader, io.BufferedWriter, io.TextIOWrapper, typing.IO[typing.Any]]]
