import math

def choose(n, k):
    return math.comb(n, k)

def u(n, m):
    total = 0
    for k in range(m * n + 1):
        b = choose(n + k - 1, k)
        term = (m + 2) * b**2 + (2 * m) * b**3
        total += term
    return total

p = 3
r = 2
m = 1
val1 = u(p**r, m)
val2 = u(p**(r-1), m*p)
modulus = p**(3*r + 3) # 3^9 = 19683
diff = val1 - val2
print(f"p={p}, r={r}, m={m}, modulus={modulus}:")
print(f"  u(p^r, m) = {val1}")
print(f"  u(p^(r-1), m*p) = {val2}")
print(f"  Difference = {diff}")
print(f"  Difference % modulus = {diff % modulus}")
