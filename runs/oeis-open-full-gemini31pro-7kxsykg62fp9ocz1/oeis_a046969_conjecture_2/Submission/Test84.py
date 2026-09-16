from sage.all import is_prime, divisors, bernoulli

for n in range(50000, 100000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 0:
        m = 2*n
        # Only compute denominator! Computing full bernoulli(m) is too slow for m=100000.
        # But we only need the denominator!
        # The denominator of B_m / (m*(m-1)) is D_m * m * (m-1) / gcd(N_m, D_m * m * (m-1))
        # Wait! Is there a fast way to get the denominator?
        pass
