import math

def factorial(n):
    return math.factorial(n)

def coeff_of_log_gf_gen(m, k):
    return factorial(m * k) // (factorial(k) ** m)

def generalized_exp_coeff(d, n):
    # we want to compute up to n
    a = [0] * (n + 1)
    a[0] = 1
    for k in range(1, n + 1):
        s = 0
        for j in range(k):
            s += d(j + 1) * a[k - (j + 1)]
        a[k] = s // k  # Lean's truncating division!
    return a[n]

def b_m_int(m, n):
    if n == 0:
        return 0
    def d(k):
        return n * coeff_of_log_gf_gen(m, k)
    return generalized_exp_coeff(d, n)

# Search for counterexample!
# hp: Nat.Prime p
# hp5: p >= 5
# hm: m >= 1
# hn: n >= 1
# hr: r >= 1

primes = [5, 7, 11, 13]
for m in [1, 2, 3]:
    for p in primes:
        for n in [1, 2, 3, 4, 5]:
            for r in [1, 2]:
                val1 = b_m_int(m, n * (p ** r))
                val2 = b_m_int(m, n * (p ** (r - 1)))
                modulus = p ** (3 * r)
                diff = val1 - val2
                if diff % modulus != 0:
                    print(f"COUNTEREXAMPLE FOUND!")
                    print(f"m = {m}")
                    print(f"n = {n}")
                    print(f"r = {r}")
                    print(f"p = {p}")
                    print(f"val1 = {val1}")
                    print(f"val2 = {val2}")
                    print(f"modulus = {modulus}")
                    print(f"diff % modulus = {diff % modulus}")
                    import sys
                    sys.exit(0)
print("No counterexample found.")
