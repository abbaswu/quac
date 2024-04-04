from datetime import time

class A(time):
    pass

def f(dt1):
    return dt1.hour(), dt1.minute(), dt1.second(), dt1.microsecond()