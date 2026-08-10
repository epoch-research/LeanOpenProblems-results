S = {2, 5/2, 3, 4, 5, 11/2, 6, 10, 11, 16, 17/2, 21, 47/2, 46}

def in_S(x):
    for s in S:
        if abs(x - s) < 1e-9:
            return True
    return False

for n in range(1, 1000):
    args = [9*n+1, 2*n+1, 1.5*n+1, 4.5*n+1, 4*n+1, 3*n+1, n+1]
    any_in = any(in_S(arg) for arg in args)
    if any_in:
        print(f"n={n} has some argument in S")
