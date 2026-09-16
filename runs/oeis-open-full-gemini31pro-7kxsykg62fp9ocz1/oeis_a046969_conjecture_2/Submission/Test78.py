from sage.all import bernoulli, is_prime

def check_n(n):
    m = 2 * n
    k = m * (m - 1)
    an = (bernoulli(m) / k).denominator()
    if an % 12 != 0: return False
    p = an // 12
    if not is_prime(p): return False
    
    an_minus_1 = (bernoulli(2*(n-1)) / (2*(n-1)*(2*(n-1)-1))).denominator()
    if an_minus_1 % 12 != 0: return True
    an_plus_2 = (bernoulli(2*(n+2)) / (2*(n+2)*(2*(n+2)-1))).denominator()
    if an_plus_2 % 12 != 0: return True
    
    c1 = ((an_minus_1 // 12) - (n - 1)) % 6 == 0
    c2 = ((an // 12) - n) % 6 == 0
    c3 = ((an_plus_2 // 12) - (n + 2)) % 6 == 0
    
    if not (c1 and c2 and c3):
        print(f"COUNTEREXAMPLE: n={n}")
        return True
    return False

# Since p must be 1 mod 6, and n must be 1 mod 6, they might differ.
# What if n is NOT 1 mod 6?
# Can a(n)/12 be prime if n != 1 mod 6?
# Let's check if there's ANY n <= 50000 where a(n)/12 is prime and n != 1 mod 6.
