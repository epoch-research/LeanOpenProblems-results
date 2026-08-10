import math

def factorial(n):
    return math.factorial(n)

def generalized_choose_int(r, k):
    if k == 0:
        return 1
    prod = 1
    for i in range(k):
        prod *= (r - i)
    return prod // factorial(k)

def generalized_catalan_coefficient(r, k):
    if k == 0:
        return 1
    num_choose = generalized_choose_int(r + 2 * k - 1, k)
    denominator = r + k
    if denominator == 0:
        return 0
    return (r * num_choose) // denominator

def a_gen(m, n):
    if n == 0:
        return 1
    r = m * n
    s = 0
    for k in range(n + 1):
        s += generalized_catalan_coefficient(r, k)
    return s

def check_conjecture(m, p, n, k_exp):
    val1 = a_gen(m, n * (p ** k_exp))
    val2 = a_gen(m, n * (p ** (k_exp - 1)))
    mod_val = p ** (3 * k_exp)
    diff = val1 - val2
    is_congruent = (diff % mod_val) == 0
    print(f"m={m}, p={p}, n={n}, k={k_exp}: val1={val1}, val2={val2}, diff={diff}, mod={mod_val}, congruent={is_congruent}")
    return is_congruent

m = -3
row = []
for n in range(21):
    row.append(a_gen(m, n))
print(f"m={m}: {row}")
