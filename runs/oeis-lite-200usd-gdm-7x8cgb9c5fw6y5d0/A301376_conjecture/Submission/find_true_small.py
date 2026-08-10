import math
from sympy import factorint

def is_sum_of_two_squares(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def has_actual_solution(N):
    N2 = N * N
    # Max v is such that 2^(v-1) <= N
    max_v = int(math.log2(N)) + 2
    for v in range(max_v + 1):
        for u in range(v + 1):
            if (2**v - 2**u) % 6 == 0:
                x = (2**v + 2**u) // 2
                y = (2**v - 2**u) // 6
                val = x*x + y*y
                if val <= N2:
                    if is_sum_of_two_squares(N2 - val):
                        return True
    return False

print("Searching for the smallest true counterexample N...")
for N in range(1, 100000):
    if not has_actual_solution(N):
        print(f"FOUND TRUE COUNTEREXAMPLE N = {N}")
        break
