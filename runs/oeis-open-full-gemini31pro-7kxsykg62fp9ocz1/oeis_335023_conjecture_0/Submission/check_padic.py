def vp(n, p):
    cnt = 0
    while n > 0 and n % p == 0:
        cnt += 1
        n //= p
    return cnt

def vp_F(n, p):
    # F(n) = n! * sum_{k=2}^n (-1)^k / k
    # We compute F(n) exactly
    import math
    s = sum((-1)**k * math.factorial(n) // k for k in range(2, n+1))
    return vp(s, p)

def vp_fact(n, p):
    cnt = 0
    while n > 0:
        cnt += n // p
        n //= p
    return cnt

for p in [3, 5, 7, 11, 13, 17, 19]:
    n = p**2 - 1
    # A(n) = gcd(F(n), n!)
    # We only care about the power of p in A(n).
    vA_n = min(vp_F(n, p), vp_fact(n, p))
    vA_n_plus_1 = min(vp_F(n+1, p), vp_fact(n+1, p))
    print(f"p={p}, v_p(A(p^2-1))={vA_n}, v_p(A(p^2))={vA_n_plus_1}, diff={vA_n_plus_1 - vA_n}")
