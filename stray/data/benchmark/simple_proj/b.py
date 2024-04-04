from .a import A
import data.benchmark.simple_proj as simple_proj

def f():
    return simple_proj.x

def g():
    return A(1).f()