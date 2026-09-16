import math

def M(n):
    return max(min(math.comb(n, k), 2**k) for k in range(n + 1))

def a(n):
    return sum((math.comb(n, k) % (2**k)) for k in range(1, n + 1))

for n in [10, 20, 30, 40, 50, 60, 70, 80, 90, 100]:
    Mn = M(n)
    an = a(n)
    print(f"n={n}, Mn={Mn}, an={an}, an/Mn={an/Mn:.3f}")
