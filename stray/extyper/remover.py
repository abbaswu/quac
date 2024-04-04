import ast
import astunparse

source="""
# -*- coding: utf-8 -*-


# Import modules
import numpy as np

from .base import Lifeform

class ChaCha(Lifeform):
    
    def ___init___(self):
        super(ChaCha, self).__init__()
        
    @property
    def layout(self):
        X = np.zeros((6,8))
        X[0,4] = 1
        X[1,2::2] = 1
        X[2,::2] = 1
        X += np.rot90(X, 2)
        return X
"""

class TypeHintRemover(ast.NodeTransformer):
    def visit_FunctionDef(self, node):
        # remove the return type defintion
        node.returns = None
        # remove all argument annotations
        if node.args.args:
            for arg in node.args.args:
                arg.annotation = None
        return node

    # def visit_Import(self, node):
    #     node.names = [n for n in node.names if n.name != 'typing']
    #     return node if node.names else None

    # def visit_ImportFrom(self, node):
    #     return node if node.module != 'typing' else None

# parse the source code into an AST
# parsed_source = ast.parse(source)
# # remove all type annotations, function return type definitions
# # and import statements from 'typing'
# transformed = TypeHintRemover().visit(parsed_source)
# # convert the AST back to source code
# print(ast.unparse(transformed))