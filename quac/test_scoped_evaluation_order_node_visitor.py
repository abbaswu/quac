"""
To generate an HTML coverage report:

- Run Coverage: coverage run --source=scoped_evaluation_order_node_visitor test_scoped_evaluation_order_node_visitor.py
- Generate an HTML report: coverage html
"""

import ast

from scoped_evaluation_order_node_visitor import scoped_evaluation_order_node_visitor


CODE = '''
class Wrapper:
    def __init__(self, v):
        self._value = v
    def value(self):
        return self._value

def f(x, y):
    return Wrapper(x.value() + y.value())


def make_cumulative(table):
    P = []; C = []; prob = 0.
    for char, p in table:
        prob += p; P += [prob]; C += [ord(char)]
    return (P, C)


def keyword_arguments_for(
    self,
    parameters,
    arguments = None,
):
    if arguments is None: arguments = {}
    for param, required in parameters.items():
        if param in arguments: continue
        try:
            arguments[param] = getattr(self, param)
        except AttributeError as exc:
            pass
    return arguments


x = 10
with open('file.txt') as f:
    data = f.read()
y = MyClass().my_method()
z: int = (result := x + y)  # Named expression
dict_comp = {i: i**2 for i in range(5)}  # Dictionary comprehension
[i for i in range(z) if i % 2]
'''


VISIT_RESULT = [
  [
    [],
    "Module",
    "class Wrapper:\n\n    def __init__(self, v):\n        self._value = v\n\n    def value(self):\n        return self._value\n\ndef f(x, y):\n    return Wrapper(x.value() + y.value())\n\ndef make_cumulative(table):\n    P = []\n    C = []\n    prob = 0.0\n    for (char, p) in table:\n        prob += p\n        P += [prob]\n        C += [ord(char)]\n    return (P, C)\n\ndef keyword_arguments_for(self, parameters, arguments=None):\n    if arguments is None:\n        arguments = {}\n    for (param, required) in parameters.items():\n        if param in arguments:\n            continue\n        try:\n            arguments[param] = getattr(self, param)\n        except AttributeError as exc:\n            pass\n    return arguments\nx = 10\nwith open('file.txt') as f:\n    data = f.read()\ny = MyClass().my_method()\nz: int = (result := (x + y))\ndict_comp = {i: i ** 2 for i in range(5)}\n[i for i in range(z) if i % 2]"
  ],
  [
    [],
    "ClassDef",
    "class Wrapper:\n\n    def __init__(self, v):\n        self._value = v\n\n    def value(self):\n        return self._value"
  ],
  [
    [
      "ClassDef"
    ],
    "FunctionDef",
    "def __init__(self, v):\n    self._value = v"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "arg",
    "self"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "arg",
    "v"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "arguments",
    "self, v"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Name",
    "v"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Name",
    "self"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Attribute",
    "self._value"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Assign",
    "self._value = v"
  ],
  [
    [
      "ClassDef"
    ],
    "FunctionDef",
    "def value(self):\n    return self._value"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "arg",
    "self"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "arguments",
    "self"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Name",
    "self"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Attribute",
    "self._value"
  ],
  [
    [
      "ClassDef",
      "FunctionDef"
    ],
    "Return",
    "return self._value"
  ],
  [
    [],
    "FunctionDef",
    "def f(x, y):\n    return Wrapper(x.value() + y.value())"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "x"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "y"
  ],
  [
    [
      "FunctionDef"
    ],
    "arguments",
    "x, y"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "Wrapper"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "x"
  ],
  [
    [
      "FunctionDef"
    ],
    "Attribute",
    "x.value"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "x.value()"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "y"
  ],
  [
    [
      "FunctionDef"
    ],
    "Attribute",
    "y.value"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "y.value()"
  ],
  [
    [
      "FunctionDef"
    ],
    "BinOp",
    "x.value() + y.value()"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "Wrapper(x.value() + y.value())"
  ],
  [
    [
      "FunctionDef"
    ],
    "Return",
    "return Wrapper(x.value() + y.value())"
  ],
  [
    [],
    "FunctionDef",
    "def make_cumulative(table):\n    P = []\n    C = []\n    prob = 0.0\n    for (char, p) in table:\n        prob += p\n        P += [prob]\n        C += [ord(char)]\n    return (P, C)"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "table"
  ],
  [
    [
      "FunctionDef"
    ],
    "arguments",
    "table"
  ],
  [
    [
      "FunctionDef"
    ],
    "List",
    "[]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "P"
  ],
  [
    [
      "FunctionDef"
    ],
    "Assign",
    "P = []"
  ],
  [
    [
      "FunctionDef"
    ],
    "List",
    "[]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "C"
  ],
  [
    [
      "FunctionDef"
    ],
    "Assign",
    "C = []"
  ],
  [
    [
      "FunctionDef"
    ],
    "Constant",
    "0.0"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "prob"
  ],
  [
    [
      "FunctionDef"
    ],
    "Assign",
    "prob = 0.0"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "table"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "char"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "p"
  ],
  [
    [
      "FunctionDef"
    ],
    "Tuple",
    "(char, p)"
  ],
  [
    [
      "FunctionDef"
    ],
    "For",
    "for (char, p) in table:\n    prob += p\n    P += [prob]\n    C += [ord(char)]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "p"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "prob"
  ],
  [
    [
      "FunctionDef"
    ],
    "AugAssign",
    "prob += p"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "prob"
  ],
  [
    [
      "FunctionDef"
    ],
    "List",
    "[prob]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "P"
  ],
  [
    [
      "FunctionDef"
    ],
    "AugAssign",
    "P += [prob]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "ord"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "char"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "ord(char)"
  ],
  [
    [
      "FunctionDef"
    ],
    "List",
    "[ord(char)]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "C"
  ],
  [
    [
      "FunctionDef"
    ],
    "AugAssign",
    "C += [ord(char)]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "P"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "C"
  ],
  [
    [
      "FunctionDef"
    ],
    "Tuple",
    "(P, C)"
  ],
  [
    [
      "FunctionDef"
    ],
    "Return",
    "return (P, C)"
  ],
  [
    [],
    "FunctionDef",
    "def keyword_arguments_for(self, parameters, arguments=None):\n    if arguments is None:\n        arguments = {}\n    for (param, required) in parameters.items():\n        if param in arguments:\n            continue\n        try:\n            arguments[param] = getattr(self, param)\n        except AttributeError as exc:\n            pass\n    return arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "self"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "parameters"
  ],
  [
    [
      "FunctionDef"
    ],
    "arg",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Constant",
    "None"
  ],
  [
    [
      "FunctionDef"
    ],
    "arguments",
    "self, parameters, arguments=None"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Constant",
    "None"
  ],
  [
    [
      "FunctionDef"
    ],
    "Compare",
    "arguments is None"
  ],
  [
    [
      "FunctionDef"
    ],
    "If",
    "if arguments is None:\n    arguments = {}"
  ],
  [
    [
      "FunctionDef"
    ],
    "Dict",
    "{}"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Assign",
    "arguments = {}"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "parameters"
  ],
  [
    [
      "FunctionDef"
    ],
    "Attribute",
    "parameters.items"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "parameters.items()"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "param"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "required"
  ],
  [
    [
      "FunctionDef"
    ],
    "Tuple",
    "(param, required)"
  ],
  [
    [
      "FunctionDef"
    ],
    "For",
    "for (param, required) in parameters.items():\n    if param in arguments:\n        continue\n    try:\n        arguments[param] = getattr(self, param)\n    except AttributeError as exc:\n        pass"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "param"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Compare",
    "param in arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "If",
    "if param in arguments:\n    continue"
  ],
  [
    [
      "FunctionDef"
    ],
    "Continue",
    "continue"
  ],
  [
    [
      "FunctionDef"
    ],
    "Try",
    "try:\n    arguments[param] = getattr(self, param)\nexcept AttributeError as exc:\n    pass"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "getattr"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "self"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "param"
  ],
  [
    [
      "FunctionDef"
    ],
    "Call",
    "getattr(self, param)"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "param"
  ],
  [
    [
      "FunctionDef"
    ],
    "Subscript",
    "arguments[param]"
  ],
  [
    [
      "FunctionDef"
    ],
    "Assign",
    "arguments[param] = getattr(self, param)"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "AttributeError"
  ],
  [
    [
      "FunctionDef"
    ],
    "ExceptHandler",
    "except AttributeError as exc:\n    pass"
  ],
  [
    [
      "FunctionDef"
    ],
    "Pass",
    "pass"
  ],
  [
    [
      "FunctionDef"
    ],
    "Name",
    "arguments"
  ],
  [
    [
      "FunctionDef"
    ],
    "Return",
    "return arguments"
  ],
  [
    [],
    "Constant",
    "10"
  ],
  [
    [],
    "Name",
    "x"
  ],
  [
    [],
    "Assign",
    "x = 10"
  ],
  [
    [],
    "Name",
    "open"
  ],
  [
    [],
    "Constant",
    "'file.txt'"
  ],
  [
    [],
    "Call",
    "open('file.txt')"
  ],
  [
    [],
    "Name",
    "f"
  ],
  [
    [],
    "withitem",
    "open('file.txt') as f"
  ],
  [
    [],
    "With",
    "with open('file.txt') as f:\n    data = f.read()"
  ],
  [
    [],
    "Name",
    "f"
  ],
  [
    [],
    "Attribute",
    "f.read"
  ],
  [
    [],
    "Call",
    "f.read()"
  ],
  [
    [],
    "Name",
    "data"
  ],
  [
    [],
    "Assign",
    "data = f.read()"
  ],
  [
    [],
    "Name",
    "MyClass"
  ],
  [
    [],
    "Call",
    "MyClass()"
  ],
  [
    [],
    "Attribute",
    "MyClass().my_method"
  ],
  [
    [],
    "Call",
    "MyClass().my_method()"
  ],
  [
    [],
    "Name",
    "y"
  ],
  [
    [],
    "Assign",
    "y = MyClass().my_method()"
  ],
  [
    [],
    "Name",
    "x"
  ],
  [
    [],
    "Name",
    "y"
  ],
  [
    [],
    "BinOp",
    "x + y"
  ],
  [
    [],
    "Name",
    "result"
  ],
  [
    [],
    "NamedExpr",
    "(result := (x + y))"
  ],
  [
    [],
    "Name",
    "int"
  ],
  [
    [],
    "Name",
    "z"
  ],
  [
    [],
    "AnnAssign",
    "z: int = (result := (x + y))"
  ],
  [
    [
      "DictComp"
    ],
    "Name",
    "range"
  ],
  [
    [
      "DictComp"
    ],
    "Constant",
    "5"
  ],
  [
    [
      "DictComp"
    ],
    "Call",
    "range(5)"
  ],
  [
    [
      "DictComp"
    ],
    "Name",
    "i"
  ],
  [
    [
      "DictComp"
    ],
    "comprehension",
    "for i in range(5)"
  ],
  [
    [
      "DictComp"
    ],
    "Name",
    "i"
  ],
  [
    [
      "DictComp"
    ],
    "Name",
    "i"
  ],
  [
    [
      "DictComp"
    ],
    "Constant",
    "2"
  ],
  [
    [
      "DictComp"
    ],
    "BinOp",
    "i ** 2"
  ],
  [
    [],
    "DictComp",
    "{i: i ** 2 for i in range(5)}"
  ],
  [
    [],
    "Name",
    "dict_comp"
  ],
  [
    [],
    "Assign",
    "dict_comp = {i: i ** 2 for i in range(5)}"
  ],
  [
    [
      "ListComp"
    ],
    "Name",
    "range"
  ],
  [
    [
      "ListComp"
    ],
    "Name",
    "z"
  ],
  [
    [
      "ListComp"
    ],
    "Call",
    "range(z)"
  ],
  [
    [
      "ListComp"
    ],
    "Name",
    "i"
  ],
  [
    [
      "ListComp"
    ],
    "comprehension",
    "for i in range(z) if i % 2"
  ],
  [
    [
      "ListComp"
    ],
    "Name",
    "i"
  ],
  [
    [
      "ListComp"
    ],
    "Constant",
    "2"
  ],
  [
    [
      "ListComp"
    ],
    "BinOp",
    "i % 2"
  ],
  [
    [
      "ListComp"
    ],
    "Name",
    "i"
  ],
  [
    [],
    "ListComp",
    "[i for i in range(z) if i % 2]"
  ],
  [
    [],
    "Expr",
    "[i for i in range(z) if i % 2]"
  ]
]

l = []




if __name__ == '__main__':
    actual_visit_result = []

    def callback_(node, scope_stack):
        unparsed_node = ast.unparse(node).strip()

        if unparsed_node:
            scope_stack_classe_names = [type(s).__name__ for s in scope_stack]
            node_class_name = type(node).__name__

            actual_visit_result.append([scope_stack_classe_names, node_class_name, unparsed_node])
        
    scoped_evaluation_order_node_visitor(
        ast.parse(CODE),
        callback_
    )

    assert actual_visit_result == VISIT_RESULT
