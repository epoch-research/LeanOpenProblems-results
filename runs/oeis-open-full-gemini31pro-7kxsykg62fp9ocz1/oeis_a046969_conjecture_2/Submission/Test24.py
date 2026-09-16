from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(7, 200, 6):
    an = a(n)
    p = an // 12
    if is_prime(p):
        print(f"n={n}, p={p}, p mod 6 = {p % 6}")
