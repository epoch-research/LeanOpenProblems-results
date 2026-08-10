import math

def choose(n, k):
    return math.comb(n, k)

def b(n, k):
    val = n + k - 1
    if val < 0:
        val = 0
    return choose(val, k)

p = 3
r = 2
n = p**r
prev_n = p**(r-1)
modulus = p**(3*r + 3) # 3^9 = 19683

S1 = 0
for k in range(1, n + 1):
    if k % p != 0:
        bk = b(n, k)
        term = 3 * bk**2 + 2 * bk**3
        S1 += term

S2 = 0
for j in range(1, prev_n + 1):
    bk = b(n, p * j)
    term = 3 * bk**2 + 2 * bk**3
    S2 += term

S3 = 0
for j in range(1, prev_n + 1):
    bk = b(prev_n, j)
    term = 3 * bk**2 + 2 * bk**3
    S3 += term

print("S1 mod 3^9:", S1 % modulus)
print("(S2 - S3) mod 3^9:", (S2 - S3) % modulus)
print("(S1 + S2 - S3) mod 3^9:", (S1 + S2 - S3) % modulus)
