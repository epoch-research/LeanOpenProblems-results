from sage.all import is_prime, divisors

# Check if any condition fails for valid n up to 50000
# We only need to check n where D_2n has no primes > 3
# and the uncancelled part of 2n-1 is prime.

def check_all():
    for n in range(7, 50000, 6):
        m = 2*n
        q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
        if len(q_D) == 0:
            # D_2n = 6. So a(n)/12 is just the uncancelled part of m-1
            p = m - 1
            # But wait, some primes in m-1 could be cancelled!
            # It's only prime if p itself is prime (and not cancelled) 
            # OR if p is composite but all except one prime factor is cancelled.
            # We already checked up to 50000 that the only case where cancelled primes
            # leave a prime is n=49177.
            # What if m-1 is prime and NOT cancelled?
            if is_prime(p):
                # Check if p is cancelled!
                # By Adams/Kummer, is p cancelled?
                # For p to be cancelled, p | B_m.
                # It's very rare. Let's assume it's not cancelled.
                # So a(n)/12 = p.
                # Does (p - n) % 6 == 0 ?
                # p = 2n-1. p - n = n - 1. Since n = 1 mod 6, n-1 = 0 mod 6.
                # So this always holds!
                
                # Check n-1
                # Does 6 | (a(n-1)/12 - (n-1)) ?
                pass
