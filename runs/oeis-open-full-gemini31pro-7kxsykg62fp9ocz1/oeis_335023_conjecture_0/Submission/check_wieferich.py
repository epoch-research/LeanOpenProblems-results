import math

def F_mod_p(n, p):
    if n < 2: return 0
    # We want F(n) mod p. But F(n) = n! * sum_{k=2}^n (-1)^k / k
    # This is easy if n < p. If n >= p, n! is 0 mod p, 
    # but the sum might have denominators divisible by p.
    pass

# Let's compute a(p^2-1) mod something?
