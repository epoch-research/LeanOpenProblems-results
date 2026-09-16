from sage.all import is_prime, divisors, factor, bernoulli

# Find n = 1 mod 6 where D_2n = 6
# Then check if a(n)/12 is prime and = 5 mod 6.
# Actually, just find any n where p = a(n)/12 is = 5 mod 6!

def check():
    for n in range(7, 5000, 6):
        q_D = [d+1 for d in divisors(2*n) if d+1 > 3 and is_prime(d+1)]
        if len(q_D) == 0:
            m = 2*n
            # compute gcd(N_m, m-1)
            # Since we only need N_m mod (m-1), we can compute it efficiently?
            # Actually for n up to 5000, we can just use bernoulli
            b = bernoulli(m) / (m*(m-1))
            an = b.denominator()
            if an % 12 == 0:
                p = an // 12
                if is_prime(p):
                    if p % 6 == 5:
                        print(f"COUNTEREXAMPLE: n={n}, p={p}")
                        return
check()
print("Done")
