
from abc import ABCMeta
from typing import Callable

RESERVED:str = 'RESERVED'


class Parser(metaclass=ABCMeta):
    def __add__(self, other):
        return Concat(self, other)

    def __mul__(self, other):
        return Exp(self, other)

    def __or__(self, other):
        return Alternate(self, other)

    def __xor__(self, function):
        return Process(self, function)

    def __call__(self, tokens, pos):
        pass


class Process(Parser):
    parser:Parser
    separator:Callable
    def __init__(self, parser, function):
        self.parser = parser
        self.function = function

    # def __call__(self, tokens, pos):
    #     result = self.parser(tokens, pos)
    #     if result:
    #         arg = result.value
    #         result.value = self.function(arg)
    #         return result
class Exp(Parser):
    parser:Parser
    separator:Parser
    def __init__(self, parser, separator):
        self.parser = parser
        self.separator = separator

    # def __call__(self, tokens, pos):
    #     result = self.parser(tokens, pos)

    #     def process_next(parsed):
    #         (sepfunc, right) = parsed
    #         return sepfunc(result.value, right)
    #     next_parser = self.separator + self.parser ^ process_next

    #     next_result = result
    #     while next_result:
    #         next_result = next_parser(tokens, result.pos)
    #         if next_result:
    #             result = next_result
    #     return result

class Concat(Parser):
    left:Parser
    right:Parser
    def __init__(self, left, right):
        self.left = left
        self.right = right

    # def __call__(self, tokens, pos):
    #     left_result = self.left(tokens, pos)
    #     if left_result:
    #         right_result = self.right(tokens, left_result.pos)
    #         if right_result:
    #             combined_value = (left_result.value, right_result.value)
    #             return Result(combined_value, right_result.pos)
    #     return None


class Alternate(Parser):
    left:Parser
    right:Parser
    def __init__(self, left, right):
        self.left = left
        self.right = right

    # def __call__(self, tokens, pos):
    #     left_result = self.left(tokens, pos)
    #     if left_result:
    #         return left_result
    #     else:
    #         right_result = self.right(tokens, pos)
    #         return right_result
class Reserved(Parser):
    value:str
    tag:str
    def __init__(self, value, tag):
        self.value = value
        self.tag = tag

    # def __call__(self, tokens, pos):
    #     if pos < len(tokens) and \
    #        tokens[pos][0] == self.value and \
    #        tokens[pos][1] is self.tag:
    #         return Result(tokens[pos][0], pos + 1)
    #     else:
    #         return None

def keyword(kw):
    return Reserved(kw, RESERVED)

def any_operator_in_list(ops):
    op_parsers = [keyword(op) for op in ops]
    parser = op_parsers[0]
    for op in op_parsers[1:]:
        parser |= op
    return parser



def process_logic(op):
    if op == 'and':
        return lambda l, r: AndBexp(l, r)
    elif op == 'or':
        return lambda l, r: OrBexp(l, r)
    else:
        raise RuntimeError('unknown logic operator: ' + op)
def op_parser(precedence_level, combine):
    return any_operator_in_list(precedence_level) ^ combine

def precedence(value_parser, precedence_levels, combine):

    parser = value_parser * op_parser(precedence_levels[0], combine)
    for precedence_level in precedence_levels[1:]:
        parser = parser * op_parser(precedence_level, combine)
    return parser
