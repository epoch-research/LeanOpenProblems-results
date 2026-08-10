import math
import numpy as np

def main():
    limit = 2000005
    print("Computing totients...", flush=True)
    phi = np.arange(limit, dtype=np.int64)
    for i in range(2, limit):
        if phi[i] == i:
            for j in range(i, limit, i):
                phi[j] -= phi[j] // i
    print("Done.", flush=True)

    # Sieve to find primes up to 2 million
    print("Sieve for primes...", flush=True)
    is_prime = [True] * limit
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            for j in range(i*i, limit, i):
                is_prime[j] = False
    print("Done.", flush=True)

    def is_square(x):
        r = int(math.isqrt(x))
        return r * r == x

    uncovered_without_prime_n_minus_k = []
    
    print("Checking uncovered numbers...", flush=True)
    for n in range(9, 2000001):
        if n % 3 == 0 or n % 10 == 0:
            continue
        
        limit_k = (n - 1) // 2
        found = False
        # We search for k such that phi(k)*phi(n-k) is square AND n-k is prime
        for k in range(1, limit_k + 1):
            if is_prime[n - k]:
                prod = int(phi[k]) * int(phi[n - k])
                if is_square(prod):
                    found = True
                    break
        if not found:
            uncovered_without_prime_n_minus_k.append(n)
            
    print(f"Total uncovered n: {1199994}")
    print(f"Uncovered n without prime n-k: {len(uncovered_without_prime_n_minus_k)}")
    if len(uncovered_without_prime_n_minus_k) > 0:
        print(f"First 50 exceptions: {uncovered_without_prime_n_minus_k[:50]}")

if __name__ == "__main__":
    main()
