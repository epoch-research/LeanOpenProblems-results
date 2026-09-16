from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(7, 50, 6):
    an = a(n)
    print(f"n={n}")
    print(f"  a(n-1)/12 mod 6 = {(a(n-1)//12)%6}")
    print(f"  a(n)/12 mod 6   = {(an//12)%6}")
    print(f"  a(n+2)/12 mod 6 = {(a(n+2)//12)%6}")
