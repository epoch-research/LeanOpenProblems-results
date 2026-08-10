import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0: return False
    return True

n = 1935
for p in range(2, n):
    if is_prime(p):
        q = math.isqrt(n + p)
        if is_prime(q):
            print(f"p = {p}, n+p = {n+p}, sqrt(n+p) = {q}")
