import math

p = 1093
s = 0
for m in range(2, p):
    s += (-1)**m * math.factorial(p-1) // m

print("F(p-1) mod p:", s % p)
print("F(p-1) - (p-1)! mod p:", (s - math.factorial(p-1)) % p)
