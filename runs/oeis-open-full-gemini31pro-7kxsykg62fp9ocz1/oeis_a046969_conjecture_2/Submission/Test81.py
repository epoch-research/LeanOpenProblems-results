from sage.all import is_prime, bernoulli

for n in range(2, 2000):
    if n % 6 == 1: continue
    
    m = 2*n
    b = bernoulli(m) / (m*(m-1))
    an = b.denominator()
    if an % 12 == 0:
        p = an // 12
        if is_prime(p):
            print(f"WOW! n={n}, p={p}")
            
print("Done checking n != 1 mod 6")
