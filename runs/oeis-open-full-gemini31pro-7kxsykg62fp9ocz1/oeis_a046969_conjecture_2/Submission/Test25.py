from sage.all import bernoulli

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(7, 200, 6):
    an = a(n)
    p = an // 12
    if an % 12 == 0 and p > 1 and p == int(p) and all(p % i != 0 for i in range(2, int(p**0.5)+1)):
        # p is prime
        print(f"n={n}, p={p}, p|n: {n%p==0}, p|2n-1: {(2*n-1)%p==0}")
