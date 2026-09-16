from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

n = 2689
an = a(n)
print(f"n={n}")
print(f"a(n)/12 = {an // 12}")
print(f"is_prime? {is_prime(an // 12)}")
print(f"2n-1 = {2*n-1}")
