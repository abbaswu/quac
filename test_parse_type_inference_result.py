"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=parse_type_inference_result test_parse_type_inference_result.py
- Generate an HTML report: coverage html

References:

- https://chat.openai.com/share/0977e84d-91b6-4e2b-addc-0cc53a0ff5da
"""

from parse_type_inference_result import parse

if __name__ == '__main__':
    assert parse('builtins.NoneType') == parse('None')
    assert str(parse('builtins.NoneType')) == 'None'
    assert parse('builtins.ellipsis') == parse('...')
    assert str(parse('builtins.ellipsis')) == '...'
    assert str(
        parse('typing.Generator[builtins.tuple[builtins.list[typing.Any], typing.Any], typing.Any, typing.Any]')
    ) == 'typing.Generator[builtins.tuple[builtins.list[typing.Any], typing.Any], typing.Any, typing.Any]'
    assert str(
        parse('typing.Callable[..., typing.Any]')
    ) == 'typing.Callable[..., typing.Any]'
    assert str(
        parse('typing.Callable[[], typing.Any]')
    ) == 'typing.Callable[[], typing.Any]'
    assert str(
        parse('typing.Callable[[typing.Any], typing.Any]')
    ) == 'typing.Callable[[typing.Any], typing.Any]'
    assert str(
        parse('typing.Callable[[typing.Any, typing.Any], typing.Any]')
    ) == 'typing.Callable[[typing.Any, typing.Any], typing.Any]'
