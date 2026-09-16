from sage.all import is_prime, factor, bernoulli

# Find n = 1 mod 6 where a(n)/12 is prime and p = 5 mod 6
def check_n(n):
    m = 2*n
    b = bernoulli(m) / (m*(m-1))
    an = b.denominator()
    if an % 12 != 0: return False
    p = an // 12
    if is_prime(p):
        print(f"n={n}, p={p}, p mod 6 = {p%6}")
        if p % 6 != 1:
            print("COUNTEREXAMPLE!")
            return True
    return False

for n in range(7, 50000, 6):
    # Quick filter: D_2n can have at most one prime > 3.
    # Actually, D_2n MUST have NO primes > 3, because we need a(n) = 12p, and 12 already comes from 2,3.
    # Wait, if D_2n has a prime q > 3, then q | a(n). Then q must be p.
    # But then n(2n-1) must be COMPLETELY cancelled by N_{2n}.
    pass
