def A(n):
    return len(set(x**2 % n for x in range(n)))

for n in range(4, 100):
    if all(n % p != 0 for p in range(2, n)): continue # skip primes
    a = A(n)
    print(f"n={n}, A(n)={a}, max={n/2+1}, bound={a*(a-1)}, n^2-1={n**2-1}, ratio={(n**2-1)/(a*(a-1)) if a>1 else 'inf'}")
