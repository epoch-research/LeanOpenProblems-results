import math

from sympy import factorint

def is_sum_of_two_squares(n):
    if n < 0: return False
    if n == 0: return True
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs > limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val > limit:
                break
            V.add(val)
    return sorted(list(V))

# Search for the smallest N > 0 where a(N) = 0
for N in range(1, 1000):
    if N % 50 == 0:
        print(f"Checking N = {N}...", flush=True)
    N2 = N*N
    V_all = get_V_all(N2)
    any_sol = False
    for v in V_all:
        if is_sum_of_two_squares(N2 - v):
            any_sol = True
            break
    if not any_sol:
        print(f"FOUND COUNTEREXAMPLE! N = {N}")
        break
