from sympy import binomial, isprime

memo = {}
def A108625(n, k):
    if (n, k) in memo:
        return memo[(n, k)]
    ans = sum(binomial(n, i)**2 * binomial(n + k - i, k - i) for i in range(k + 1))
    memo[(n, k)] = ans
    return ans

memo_A = {}
def A(n):
    if n in memo_A:
        return memo_A[n]
    ans = sum(binomial(n, k)**2 * binomial(n + k, k) * A108625(n, n - k) for k in range(n + 1))
    memo_A[n] = ans
    return ans

for p in range(5, 500):
    if isprime(p):
        n = 1
        r = 1
        lhs1 = A(n * p**r)
        rhs1 = A(n * p**(r - 1))
        mod = p**(3 * r)
        cond1 = (lhs1 - rhs1) % mod == 0
        
        lhs2 = A(n * p**r - 1)
        rhs2 = A(n * p**(r - 1) - 1)
        cond2 = (lhs2 - rhs2) % mod == 0
        
        if not cond1 or not cond2:
            print(f"COUNTEREXAMPLE FOUND AT p={p}!!!")
            break
else:
    print("No counterexamples found up to 500.")
