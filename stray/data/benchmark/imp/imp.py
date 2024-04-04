# Copyright (c) 2011, Jay Conrod.
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of Jay Conrod nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL JAY CONROD BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

# import lexer




from abc import ABCMeta, abstractmethod
import sys
import re
from typing import Callable, Dict, List, Tuple, Union

# token expr is List[tuple], can only be inferred from calling. 
def lex(characters, token_exprs):
    pos = 0
    tokens = []
    while pos < len(characters):
        match = None
        for token_expr in token_exprs:
            pattern, tag = token_expr
            regex = re.compile(pattern)
            match = regex.match(characters, pos)
            if match:
                text = match.group(0)
                if tag:
                    token = (text, tag)
                    tokens.append(token)
                break
        if not match:
            sys.stderr.write('Illegal character: %s\n' % characters[pos])
            sys.exit(1)
        else:
            pos = match.end(0)
    return tokens
RESERVED = 'RESERVED'
INT      = 'INT'
ID       = 'ID'

token_exprs = [
    (r'[ \n\t]+',              None),
    (r'#[^\n]*',               None),
    (r'\:=',                   RESERVED),
    (r'\(',                    RESERVED),
    (r'\)',                    RESERVED),
    (r';',                     RESERVED),
    (r'\+',                    RESERVED),
    (r'-',                     RESERVED),
    (r'\*',                    RESERVED),
    (r'/',                     RESERVED),
    (r'<=',                    RESERVED),
    (r'<',                     RESERVED),
    (r'>=',                    RESERVED),
    (r'>',                     RESERVED),
    (r'!=',                    RESERVED),
    (r'=',                     RESERVED),
    (r'and',                   RESERVED),
    (r'or',                    RESERVED),
    (r'not',                   RESERVED),
    (r'if',                    RESERVED),
    (r'then',                  RESERVED),
    (r'else',                  RESERVED),
    (r'while',                 RESERVED),
    (r'do',                    RESERVED),
    (r'end',                   RESERVED),
    (r'[0-9]+',                INT),
    (r'[A-Za-z][A-Za-z0-9_]*', ID),
]

def imp_lex(characters):
    return lex(characters, token_exprs)




class Result:
    value:Union[str, Tuple[str,str]] 
    pos:int 
    def __init__(self, value, pos):
        self.value = value
        self.pos = pos

    def __repr__(self):
        return 'Result(%s, %d)' % (self.value, self.pos)

class Parser(metaclass=ABCMeta):
    def __add__(self, other):
        return Concat(self, other)

    def __mul__(self, other):
        return Exp(self, other)

    def __or__(self, other):
        return Alternate(self, other)

    def __xor__(self, function):
        return Process(self, function)

    # Edit: abc
    @abstractmethod 
    def __call__(self, tokens:List[Tuple[str,str]], pos:int)->Result:
        pass

class Tag(Parser):
    tag:str
    def __init__(self, tag):
        self.tag = tag

    def __call__(self, tokens, pos):
        if pos < len(tokens) and tokens[pos][1] is self.tag:
            return Result(tokens[pos][0], pos + 1)
        else:
            return None

class Reserved(Parser):
    value:str
    tag:str
    def __init__(self, value, tag):
        self.value = value
        self.tag = tag

    def __call__(self, tokens, pos):
        if pos < len(tokens) and \
           tokens[pos][0] == self.value and \
           tokens[pos][1] is self.tag:
            return Result(tokens[pos][0], pos + 1)
        else:
            return None

class Concat(Parser):
    left:Parser
    right:Parser
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __call__(self, tokens, pos):
        left_result = self.left(tokens, pos)
        if left_result:
            right_result = self.right(tokens, left_result.pos)
            if right_result:
                combined_value = (left_result.value, right_result.value)
                return Result(combined_value, right_result.pos)
        return None

class Exp(Parser):
    parser:Parser
    separator:Parser
    def __init__(self, parser, separator):
        self.parser = parser
        self.separator = separator

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        def process_next(parsed):
            (sepfunc, right) = parsed
            return sepfunc(result.value, right)
        
        next_parser = self.separator + self.parser ^ process_next

        next_result = result
        while next_result:
            next_result = next_parser(tokens, result.pos)
            if next_result:
                result = next_result
        return result

class Alternate(Parser):
    left:Parser
    right:Parser
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __call__(self, tokens, pos):
        left_result = self.left(tokens, pos)
        if left_result:
            return left_result
        else:
            right_result = self.right(tokens, pos)
            return right_result

class Opt(Parser):
    parser:Parser
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result:
            return result
        else:
            return Result(None, pos)

class Rep(Parser):
    parser:Parser
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        results = []
        result = self.parser(tokens, pos)
        while result:
            results.append(result.value)
            pos = result.pos
            result = self.parser(tokens, pos)
        return Result(results, pos)

class Process(Parser):
    parser:Parser
    function:Callable
    def __init__(self, parser, function):
        self.parser = parser
        self.function = function

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result:
            arg = result.value
            result.value = self.function(arg)
            return result

class Lazy(Parser):
    parser:Parser
    parser_func:Callable
    def __init__(self, parser_func):
        self.parser = None
        self.parser_func = parser_func

    def __call__(self, tokens, pos):
        if not self.parser:
            self.parser = self.parser_func()
        return self.parser(tokens, pos)

class Phrase(Parser):
    parser:Parser 
    def __init__(self, parser):
        self.parser = parser

    def __call__(self, tokens, pos):
        result = self.parser(tokens, pos)
        if result and result.pos == len(tokens):
            return result
        else:
            return None

class Equality(metaclass=ABCMeta):
    def __eq__(self, other):
        return isinstance(other, self.__class__) and \
               self.__dict__ == other.__dict__

    def __ne__(self, other):
        return not self.__eq__(other)
    # Edit: abc
    @abstractmethod
    def eval(self, env:Dict[str,int])->int:
        pass

    
class Statement(Equality):
    pass

class Aexp(Equality):
    pass

class Bexp(Equality):
    pass

class AssignStatement(Statement):
    name:str 
    aexp:Equality 
    def __init__(self, name, aexp):
        self.name = name
        self.aexp = aexp

    def __repr__(self):
        return 'AssignStatement(%s, %s)' % (self.name, self.aexp)

    def eval(self, env):
        value = self.aexp.eval(env)
        env[self.name] = value

class CompoundStatement(Statement):
    first:Equality
    second:Equality 
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def __repr__(self):
        return 'CompoundStatement(%s, %s)' % (self.first, self.second)

    def eval(self, env):
        self.first.eval(env)
        self.second.eval(env)

class IfStatement(Statement):
    condition:Equality
    true_stmt:Equality 
    false_stmt:Equality 
    def __init__(self, condition, true_stmt, false_stmt):
        self.condition = condition
        self.true_stmt = true_stmt
        self.false_stmt = false_stmt

    def __repr__(self):
        return 'IfStatement(%s, %s, %s)' % (self.condition, self.true_stmt, self.false_stmt)

    def eval(self, env):
        condition_value = self.condition.eval(env)
        if condition_value:
            self.true_stmt.eval(env)
        else:
            if self.false_stmt:
                self.false_stmt.eval(env)

class WhileStatement(Statement):
    condition:Equality
    body:Equality
    def __init__(self, condition, body):
        self.condition = condition
        self.body = body

    def __repr__(self):
        return 'WhileStatement(%s, %s)' % (self.condition, self.body)

    def eval(self, env):
        condition_value = self.condition.eval(env)
        while condition_value:
            self.body.eval(env)
            condition_value = self.condition.eval(env)

class IntAexp(Aexp):
    i:int
    def __init__(self, i):
        self.i = i

    def __repr__(self):
        return 'IntAexp(%d)' % self.i

    def eval(self, env):
        return self.i

class VarAexp(Aexp):
    name:str
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return 'VarAexp(%s)' % self.name

    def eval(self, env):
        if self.name in env:
            return env[self.name]
        else:
            return 0

class BinopAexp(Aexp):
    op:str
    left:Equality
    right:Equality
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return 'BinopAexp(%s, %s, %s)' % (self.op, self.left, self.right)

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        value = None
        if self.op == '+':
            value = left_value + right_value
        elif self.op == '-':
            value = left_value - right_value
        elif self.op == '*':
            value = left_value * right_value
        elif self.op == '/':
            value = left_value / right_value
        else:
            raise RuntimeError('unknown operator: ' + self.op)
        return value

class RelopBexp(Bexp):
    op:str
    left:Equality
    right:Equality
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def __repr__(self):
        return 'RelopBexp(%s, %s, %s)' % (self.op, self.left, self.right)

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        value = None
        if self.op == '<':
            value = left_value < right_value
        elif self.op == '<=':
            value = left_value <= right_value
        elif self.op == '>':
            value = left_value > right_value
        elif self.op == '>=':
            value = left_value >= right_value
        elif self.op == '=':
            value = left_value == right_value
        elif self.op == '!=':
            value = left_value != right_value
        else:
            raise RuntimeError('unknown operator: ' + self.op)
        return value

class AndBexp(Bexp):

    left:Equality
    right:Equality
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return 'AndBexp(%s, %s)' % (self.left, self.right)

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        return left_value and right_value

class OrBexp(Bexp):

    left:Equality
    right:Equality
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return 'OrBexp(%s, %s)' % (self.left, self.right)

    def eval(self, env):
        left_value = self.left.eval(env)
        right_value = self.right.eval(env)
        return left_value or right_value

class NotBexp(Bexp):
    exp:Equality
    def __init__(self, exp):
        self.exp = exp

    def __repr__(self):
        return 'NotBexp(%s)' % self.exp

    def eval(self, env):
        value = self.exp.eval(env)
        return not value
# Operator keywords and precedence levels
aexp_precedence_levels = [
    ['*', '/'],
    ['+', '-'],
]

bexp_precedence_levels = [
    ['and'],
    ['or'],
]

# Basic parsers
def keyword(kw):
    return Reserved(kw, RESERVED)


num = Tag(INT) ^ (lambda i: int(i))
id2 = Tag(ID)

# parser.py 
# Edit: We exclude functions below since its about ～compiler combinator～ and we can not figure out ~ground truth annotations~ that we are confident with enough.
# Top level parser
# def imp_parse(tokens):
#     ast = parser()(tokens, 0)
#     return ast


# def parser():
#     return Phrase(stmt_list())


# # Statements
# def stmt_list():
#     separator = keyword(';') ^ (lambda x: lambda l, r: CompoundStatement(l, r))
#     return Exp(stmt(), separator)


# def stmt():
#     return assign_stmt() | \
#            if_stmt() | \
#            while_stmt()

# def assign_stmt():

#     def process(parsed):
#         ((name, _), exp) = parsed
#         return AssignStatement(name, exp)

#     return id2 + keyword(':=') + aexp() ^ process


# def if_stmt():
#     def process(parsed):
#         (((((_, condition), _), true_stmt), false_parsed), _) = parsed
#         if false_parsed:
#             (_, false_stmt) = false_parsed
#         else:
#             false_stmt = None
#         return IfStatement(condition, true_stmt, false_stmt)

#     return keyword('if') + bexp() + \
#            keyword('then') + Lazy(stmt_list) + \
#            Opt(keyword('else') + Lazy(stmt_list)) + \
#            keyword('end') ^ process


# # def while_process(parsed):
# #     ((((_, condition), _), body), _) = parsed
# #     return WhileStatement(condition, body)


# def while_stmt():
#     def process(parsed):
#         ((((_, condition), _), body), _) = parsed
#         return WhileStatement(condition, body)
#     return keyword('while') + bexp() + \
#            keyword('do') + Lazy(stmt_list) + \
#            keyword('end') ^ process


# # Boolean expressions
# def bexp():
#     return precedence(bexp_term(),
#                       bexp_precedence_levels,
#                       process_logic)


# def bexp_term():
#     return bexp_not() | \
#            bexp_relop() | \
#            bexp_group()


# def bexp_not():
#     return keyword('not') + Lazy(bexp_term) ^ (lambda parsed: NotBexp(parsed[1]))


# def bexp_relop():
#     relops = ['<', '<=', '>', '>=', '=', '!=']
#     return aexp() + any_operator_in_list(relops) + aexp() ^ process_relop


# def bexp_group():
#     return keyword('(') + Lazy(bexp) + keyword(')') ^ process_group


# # Arithmetic expressions
# def aexp():
#     return precedence(aexp_term(),
#                       aexp_precedence_levels,
#                       process_binop)


# def aexp_term():
#     return aexp_value() | aexp_group()


# def aexp_group():
#     return keyword('(') + Lazy(aexp) + keyword(')') ^ process_group


# def aexp_value():
#     return (num ^ (lambda i: IntAexp(i))) | \
#            (id2 ^ (lambda v: VarAexp(v)))


# def precedence(value_parser, precedence_levels, combine):
#     def op_parser(precedence_level):
#         return any_operator_in_list(precedence_level) ^ combine

#     parser = value_parser * op_parser(precedence_levels[0])
#     for precedence_level in precedence_levels[1:]:
#         parser = parser * op_parser(precedence_level)
#     return parser

# # Miscellaneous functions for binary and relational operators
# def process_binop(op):
#     return lambda l, r: BinopAexp(op, l, r)


# def process_relop(parsed):
#     ((left, op), right) = parsed
#     return RelopBexp(op, left, right)


# def process_logic(op):
#     if op == 'and':
#         return lambda l, r: AndBexp(l, r)
#     elif op == 'or':
#         return lambda l, r: OrBexp(l, r)
#     else:
#         raise RuntimeError('unknown logic operator: ' + op)


# def process_group(parsed):
#     ((_, p), _) = parsed
#     return p


# def any_operator_in_list(ops):
#     op_parsers = [keyword(op) for op in ops]
#     parser = op_parsers[0]
#     for op in op_parsers[1:]:
#         parser |= op
#     return parser
