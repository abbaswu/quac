"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=get_call_information test_get_call_information.py
- Generate an HTML report: coverage html
"""

import ast

from get_call_information import get_call_information


if __name__ == '__main__':
    # sum_numbers(1, 2, 3, 4)
    call = ast.parse('sum_numbers(1, 2, 3, 4)', mode='eval').body
    call_information = get_call_information(call)
    assert ast.unparse(call_information[0]) == 'sum_numbers'
    assert [ast.unparse(a) for a in call_information[1]] == ['1', '2', '3', '4']
    assert {
        k: ast.unparse(v)
        for k, v in call_information[2].items()
    } == {}
    assert not call_information[3]

    # greet("John", message="Hi")
    call = ast.parse('greet("John", message="Hi")', mode='eval').body
    call_information = get_call_information(call)
    assert ast.unparse(call_information[0]) == 'greet'
    assert [ast.unparse(a) for a in call_information[1]] == ["'John'"]
    assert {
        k: ast.unparse(v)
        for k, v in call_information[2].items()
    } == {'message': "'Hi'"}
    assert call_information[3]

    # complex_function("arg1", "arg2", "arg3", default_kwarg="not default", key1="value1", key2="value2")
    call = ast.parse('complex_function("arg1", "arg2", "arg3", default_kwarg="not default", key1="value1", key2="value2")', mode='eval').body
    call_information = get_call_information(call)
    assert ast.unparse(call_information[0]) == 'complex_function'
    assert [ast.unparse(a) for a in call_information[1]] == ["'arg1'", "'arg2'", "'arg3'"]
    assert {
        k: ast.unparse(v)
        for k, v in call_information[2].items()
    } == {'default_kwarg': "'not default'", 'key1': "'value1'", 'key2': "'value2'"}
    assert call_information[3]

    # func(a, b=c, *d, **e)
    call = ast.parse('func(a, b=c, *d, **e)', mode='eval').body
    call_information = get_call_information(call)
    assert ast.unparse(call_information[0]) == 'func'
    assert [ast.unparse(a) for a in call_information[1]] == ['a']
    assert {
        k: ast.unparse(v)
        for k, v in call_information[2].items()
    } == {'b': 'c'}
    assert call_information[3]
