from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(1, 1000):
    an = a(n)
    if an % 12 == 0:
        p = an // 12
        if is_prime(p):
            if p != 2*n - 1:
                print(f"EXCEPTION: n={n}, p={p}")
