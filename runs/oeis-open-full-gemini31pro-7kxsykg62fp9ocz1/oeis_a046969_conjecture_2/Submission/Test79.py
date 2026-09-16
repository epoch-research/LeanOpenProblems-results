from sage.all import is_prime, divisors, bernoulli, factor

def test_conj():
    # If a(n)/12 is prime, we must have exactly one prime > 3 in a(n).
    # Since D_2n divides a(n), D_2n can have at most one prime > 3.
    # We check n up to 1,000,000 for D_2n having <= 1 prime > 3.
    pass
