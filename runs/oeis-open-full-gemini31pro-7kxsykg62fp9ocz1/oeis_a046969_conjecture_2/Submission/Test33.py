from sage.all import is_prime, divisors

def count_primes_in_D(n):
    # count prime factors > 3 of D_2n
    count = 0
    for d in divisors(2*n):
        q = d + 1
        if q > 3 and is_prime(q):
            count += 1
    return count

for n in range(2, 50000):
    c = count_primes_in_D(n)
    if c >= 2:
        # D_2n has >= 2 prime factors > 3.
        # Can they be cancelled? NO! Numerator of B_2n is coprime to D_2n!
        # So a(n) will ALWAYS have these prime factors.
        pass
