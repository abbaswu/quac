class A:
    x:int
    def __init__(self, x):
        self.x = x
        
    def f(self):
        return (self,)
a:int  = 1