from sage.all import bernoulli, is_prime, factor
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing

def check_n(n):
    # We want to know if a(n)/12 is prime.
    # a(n) is the denominator of B_{2n} / (2n(2n-1)).
    # We only care if it's 12 * p, where p is prime.
    # This means the denominator of B_{2n}/2n has very few prime factors!
    pass

# Let's just compute a(n) up to n=20000 but using a faster method.
# Wait, computing B_{2n} for n=20000 is slow.
# BUT we ONLY care if a(n) / 12 is prime!
# If a(n) / 12 is prime, then a(n) has at most ONE prime factor > 3.
# This means for ALL primes q > 3, q DOES NOT divide a(n) (except for one p).
# But we know a(n) is divisible by all primes q where q-1 | 2n.
# So if there are TWO primes > 3 such that q-1 | 2n, then a(n) has at least TWO prime factors > 3.
# Then a(n)/12 CANNOT be prime!
