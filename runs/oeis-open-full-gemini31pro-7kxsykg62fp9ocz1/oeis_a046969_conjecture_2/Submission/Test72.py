from sage.all import primes, bernoulli
for r in primes(3, 1000):
    for k in range(2, r-1, 2):
        if k % 12 == 2:
            if (bernoulli(k)/k).numerator() % r == 0:
                print(f"FOUND! r={r}, k={k}")
