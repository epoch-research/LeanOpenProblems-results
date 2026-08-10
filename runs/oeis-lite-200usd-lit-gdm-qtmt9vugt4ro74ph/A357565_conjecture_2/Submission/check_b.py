import math

def choose(n, k):
    return math.comb(n, k)

def b(n, k):
    val = n + k - 1
    if val < 0:
        val = 0
    return choose(val, k)

p = 3
r = 3
n = p**r       # 27
prev_n = p**(r-1)  # 9
modulus = p**(2*r)  # 3^6 = 729

for j in range(1, prev_n + 1):
    val1 = b(n, p * j)
    val2 = b(prev_n, j)
    diff = val1 - val2
    print(f"j = {j}:")
    print(f"  b({n}, {p*j}) = {val1}")
    print(f"  b({prev_n}, {j}) = {val2}")
    print(f"  Difference = {diff}")
    print(f"  Divisible by p^(2r) ({modulus})? {diff % modulus == 0}")
