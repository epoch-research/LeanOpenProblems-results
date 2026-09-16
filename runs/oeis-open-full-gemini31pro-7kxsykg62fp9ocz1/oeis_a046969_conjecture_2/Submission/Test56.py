from sage.all import is_prime, divisors, factor, bernoulli

for n in range(7, 20000, 6):
    q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
    if len(q_D) == 0:
        # D_2n has no primes > 3
        # We want a(n)/12 to be prime. Let's just check it!
        m = 2*n
        an = (bernoulli(m) / (m * (m-1))).denominator()
        p = an // 12
        if is_prime(p):
            print(f"n={n}, p={p}, p mod 6 = {p % 6}")
