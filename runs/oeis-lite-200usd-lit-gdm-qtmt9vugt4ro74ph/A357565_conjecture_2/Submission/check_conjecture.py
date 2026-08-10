import sympy

def choose(n, k):
    if k < 0 or k > n:
        return 0
    return sympy.binomial(n, k)

def A357565(n):
    ans = 0
    for k in range(n + 1):
        b = choose(n + k - 1, k)
        ans += 3 * b**2 + 2 * b**3
    return ans

for p in [3, 5, 7]:
    for r in [2, 3]:
        val1 = A357565(p**r)
        val2 = A357565(p**(r-1))
        modulus = p**(3*r + 3)
        diff = (val1 - val2) % modulus
        if diff != 0:
            print(f"FAILED for p={p}, r={r}! diff mod modulus = {diff}")
        else:
            print(f"Holds for p={p}, r={r}")
