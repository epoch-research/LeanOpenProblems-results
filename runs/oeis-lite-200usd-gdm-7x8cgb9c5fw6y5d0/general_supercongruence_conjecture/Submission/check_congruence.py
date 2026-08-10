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

# Let's check the congruence for some small values:
# b_m_int m (n * p^r) === b_m_int m (n * p^(r-1)) (mod p^{3r})
# hp5: p >= 5, hm: m >= 1, hn: n >= 1, hr: r >= 1

for m in [1, 2]:
    for p in [5]:
        for n in [1, 2]:
            for r in [1]:
                # r = 1
                val1 = b_m_int(m, n * (p ** r))
                val2 = b_m_int(m, n * (p ** (r - 1)))
                modulus = p ** (3 * r)
                congruent = (val1 - val2) % modulus == 0
                print(f"m={m}, p={p}, n={n}, r={r}: val1={val1}, val2={val2}, mod={modulus}, congruent={congruent}")
