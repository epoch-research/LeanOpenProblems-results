from sage.all import primes, bernoulli
P = list(primes(3, 500))
for p in P:
    for q in P:
        if p == q: continue
        if (q+1) % (p-1) == 0: continue
        if (p+1) % (q-1) == 0: continue
        
        b1 = bernoulli(q+1) / (q+1)
        if b1.numerator() % p == 0:
            b2 = bernoulli(p+1) / (p+1)
            if b2.numerator() % q == 0:
                print(f"WOW! Pair found: p={p}, q={q}")
