from sage.all import is_prime, divisors

# Check all n < 50000 where D_2n has no primes > 3
for n in range(7, 50000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 0:
        p = 2*n - 1
        if is_prime(p):
            # p is prime, so a(n)/12 is p (unless p is cancelled, which we know it isn't for p < 50000 except 49177)
            # p - n = 2n - 1 - n = n - 1 = 0 mod 6.
            pass
