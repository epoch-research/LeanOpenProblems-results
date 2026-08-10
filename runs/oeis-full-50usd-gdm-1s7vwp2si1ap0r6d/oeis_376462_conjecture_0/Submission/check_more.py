from sympy import binomial

memo = {}
def a108625_aux(n, k):
    if (n, k) in memo:
        return memo[(n, k)]
    ans = 0
    for i in range(k + 1):
        ans += binomial(n, i)**2 * binomial(n + k - i, k - i)
    memo[(n, k)] = ans
    return ans

memo_A = {}
def A376462(n):
    if n in memo_A:
        return memo_A[n]
    ans = 0
    for k in range(n + 1):
        ans += binomial(n, k)**2 * binomial(n + k, k) * a108625_aux(n, n - k)
    memo_A[n] = ans
    return ans

# Check congruence 1 and 2 for various p, n, r
tests = [
    (5, 1, 1),
    (5, 1, 2),
    (5, 2, 1),
    (7, 1, 1),
]

for p, n, r in tests:
    # Congruence 1: A(n * p^r) = A(n * p^(r-1)) mod p^(3r)
    lhs1 = A376462(n * p**r)
    rhs1 = A376462(n * p**(r - 1))
    mod = p**(3 * r)
    cond1 = (lhs1 - rhs1) % mod == 0
    
    # Congruence 2: A(n * p^r - 1) = A(n * p^(r-1) - 1) mod p^(3r)
    lhs2 = A376462(n * p**r - 1)
    rhs2 = A376462(n * p**(r - 1) - 1)
    cond2 = (lhs2 - rhs2) % mod == 0
    
    print(f"p={p}, n={n}, r={r}: Congruence 1: {cond1}, Congruence 2: {cond2}")
