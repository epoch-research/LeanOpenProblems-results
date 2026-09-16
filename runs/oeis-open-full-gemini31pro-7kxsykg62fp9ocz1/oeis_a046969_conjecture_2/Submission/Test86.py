from sage.all import primes, bernoulli

# We want to find a prime q = 5 mod 6, and a number m = 2n = 12k+2
# such that q | m-1 (so m = a*q + 1)
# and q | numerator of B_m / m.
# Then m-1 could be p * q, where p is prime and p = 5 mod 6.
# If p is prime, and D_m has no primes > 3, then n could be a counterexample!

for q in primes(5, 2000):
    if q % 6 != 5: continue
    
    # We need B_m / m = 0 mod q.
    # By Kummer's congruence, B_m / m mod q depends only on m mod (q-1).
    # Let's compute B_m / m mod q for all even m < q-1.
    for m0 in range(2, q-1, 2):
        b = bernoulli(m0) / m0
        if b.numerator() % q == 0:
            # We need m = m0 mod (q-1).
            # Also we need m = 1 mod q (so q | m-1)
            # And m = 2 mod 12 (since n = 1 mod 6, 2n = 2 mod 12)
            # Let's find such m!
            # m = m0 mod (q-1)
            # m = 1 mod q
            # m = 2 mod 12
            
            from sage.all import CRT
            # Moduli: q-1, q, 12. 
            # Note: q-1 and 12 are not coprime. Both are even.
            # q-1 is a multiple of 2. 12 is a multiple of 2.
            # We can use CRT_list
            try:
                m_val = CRT([m0, 1, 2], [q-1, q, 12])
                lcm_val = (q-1) * q * 12 // 2 # approx
                from math import gcd
                # exact lcm
                lcm_val = 1
                for md in [q-1, q, 12]:
                    lcm_val = lcm_val * md // gcd(lcm_val, md)
                
                print(f"Match: q={q}, m0={m0}, m_val={m_val}, lcm={lcm_val}")
                # We want m-1 to be p * q, where p is prime and p = 5 mod 6.
                # Let's check a few k
                for k in range(50):
                    m = m_val + k * lcm_val
                    n = m // 2
                    p = (m - 1) // q
                    from sage.all import is_prime, divisors
                    if is_prime(p) and p % 6 == 5:
                        # Check D_2n has no primes > 3
                        q_D = [d+1 for d in divisors(m) if d+1 > 3 and is_prime(d+1)]
                        if len(q_D) == 0:
                            print(f"POTENTIAL COUNTEREXAMPLE! n={n}, p={p}, q={q}")
            except Exception as e:
                pass
