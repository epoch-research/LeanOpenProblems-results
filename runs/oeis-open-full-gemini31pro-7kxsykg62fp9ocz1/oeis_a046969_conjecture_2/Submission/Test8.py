from sage.all import bernoulli, is_prime

for n in range(1, 2000):
    B = bernoulli(2*n)
    val = (B / (2*n*(2*n-1))).denominator()
    p = val // 12
    if is_prime(p):
        if n % 6 != 1:
            print(f"COUNTEREXAMPLE: n={n}, val={val}, p={p}")
            break
else:
    print("Done 2000")
