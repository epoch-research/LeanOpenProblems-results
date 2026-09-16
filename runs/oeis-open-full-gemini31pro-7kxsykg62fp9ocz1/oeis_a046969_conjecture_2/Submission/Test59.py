from sage.all import primes, bernoulli

# Search for r, s prime pairs
P = list(primes(3, 200))
for r in P:
    for s in P:
        if r == s: continue
        # check if r | numerator of B_{s+1}/(s+1)
        # Note: s+1 is even, so B_{s+1} is non-zero
        if (s+1) % (r-1) == 0: continue
        if (r+1) % (s-1) == 0: continue
        
        b1 = bernoulli(s+1) / (s+1)
        if b1.numerator() % r == 0:
            b2 = bernoulli(r+1) / (r+1)
            if b2.numerator() % s == 0:
                print(f"PAIR FOUND! r={r}, s={s}")
