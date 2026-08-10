import sympy as sp

def factorial(n):
    return sp.factorial(n)

def coeff_of_log_gf_gen(m, k):
    return factorial(m * k) // (factorial(k) ** m)

def generalized_exp_coeff(d, k):
    # k * a_k = sum_{j=1}^k d_j * a_{k-j}
    a = [sp.Integer(1)]
    for i in range(1, k + 1):
        s = sum(d(j) * a[i - j] for j in range(1, i + 1))
        a.append(s // i)
    return a[k]

def b_m_int(m, n):
    if n == 0:
        return sp.Integer(0)
    def d(k):
        return n * coeff_of_log_gf_gen(m, k)
    return generalized_exp_coeff(d, n)

# Let's check more values
for p in [5]:
    for m in [1, 2]:
        for n in [1, 2]:
            for r in [1, 2]:
                val1 = b_m_int(m, n * p**r)
                val2 = b_m_int(m, n * p**(r-1))
                diff = val1 - val2
                mod_val = p**(3*r)
                is_cong = (diff % mod_val) == 0
                print(f"m={m}, n={n}, p={p}, r={r}: {is_cong} (diff % {mod_val} = {diff % mod_val})")
