import math

# Precompute factorials
max_fact = 5000
fact = [1] * max_fact
for i in range(1, max_fact):
    fact[i] = fact[i-1] * i

def coeff_of_log_gf_gen(m, k):
    return fact[m * k] // (fact[k] ** m)

# Cache for coeff_of_log_gf_gen
coeff_cache = {}
def get_coeff(m, k):
    if (m, k) not in coeff_cache:
        coeff_cache[(m, k)] = coeff_of_log_gf_gen(m, k)
    return coeff_cache[(m, k)]

def b_m_int(m, n):
    if n == 0:
        return 0
    a = [0] * (n + 1)
    a[0] = 1
    for k in range(1, n + 1):
        s = 0
        for j in range(k):
            # d(j + 1) = n * coeff(m, j + 1)
            s += n * get_coeff(m, j + 1) * a[k - (j + 1)]
        a[k] = s // k
    return a[n]

# Fast search
print("Searching for counterexample with optimized code...")
primes = [5, 7, 11]
for m in [1, 2, 3]:
    for p in primes:
        for n in range(1, 100):
            for r in [1]:
                val1 = b_m_int(m, n * (p ** r))
                val2 = b_m_int(m, n * (p ** (r - 1)))
                modulus = p ** (3 * r)
                if (val1 - val2) % modulus != 0:
                    print(f"COUNTEREXAMPLE FOUND!")
                    print(f"m = {m}")
                    print(f"n = {n}")
                    print(f"r = {r}")
                    print(f"p = {p}")
                    print(f"val1 = {val1}")
                    print(f"val2 = {val2}")
                    print(f"modulus = {modulus}")
                    print(f"diff % modulus = {(val1 - val2) % modulus}")
                    import sys
                    sys.exit(0)
print("No counterexample found.")
