def f(x=None):
    y = [x] if x else [1]

    for yy in y:
        z = yy + 1