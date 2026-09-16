import sys

def v(p, n):
    if n == 0: return 1000000
    res = 0
    while n % p == 0:
        res += 1
        n //= p
    return res

M = 1093**2
P = 1093**1095
F = 0
fact = 1
for k in range(1, M):
    if k >= 2:
        sign = 1 if k % 2 == 0 else -1
        F = (k * F + sign * fact) % P
    fact = (fact * k) % P

print(f"v_{1093}(F) = {v(1093, F)}")
print(f"v_{1093}(fact) = {v(1093, fact)}")
