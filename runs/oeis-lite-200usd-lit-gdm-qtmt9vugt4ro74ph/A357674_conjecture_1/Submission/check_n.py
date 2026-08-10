import math

def choose(n, k):
    return math.comb(n, k)

def S1(n):
    return sum(choose(n + k - 1, k) for k in range(2 * n + 1))

def S2(n):
    return sum(choose(n + k - 1, k)**2 for k in range(2 * n + 1))

for n in range(1, 10):
    val = (3 * S2(n) + 4 * S1(n)) % n**5
    expected = 21 % n**5
    print(f"n = {n}: val = {val}, expected = {expected}, match = {val == expected}")
