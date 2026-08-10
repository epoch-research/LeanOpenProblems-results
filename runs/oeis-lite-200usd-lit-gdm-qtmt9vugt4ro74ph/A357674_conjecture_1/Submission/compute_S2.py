import math

def choose(n, k):
    return math.comb(n, k)

def S2(n):
    return sum(choose(n + k - 1, k)**2 for k in range(2 * n + 1))

seq = [S2(n) for n in range(1, 15)]
print(seq)
