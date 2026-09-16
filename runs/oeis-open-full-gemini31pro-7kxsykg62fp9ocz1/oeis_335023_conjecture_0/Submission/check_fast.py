p = 1093
# compute S_{p-1} mod p
# S = sum_{k=1}^{p-1} (-1)^k / k mod p
S = 0
for k in range(1, p):
    sign = 1 if k % 2 == 0 else -1
    inv = pow(k, p-2, p)
    S = (S + sign * inv) % p

print("S_{p-1} mod p =", S)
