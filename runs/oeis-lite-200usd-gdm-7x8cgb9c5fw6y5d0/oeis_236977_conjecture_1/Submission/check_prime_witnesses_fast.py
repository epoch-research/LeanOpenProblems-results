import math
import numpy as np

def main():
    limit = 2000005
    print("Computing totients using sieve...", flush=True)
    phi = np.arange(limit, dtype=np.int64)
    for i in range(2, limit):
        if phi[i] == i:
            for j in range(i, limit, i):
                phi[j] -= phi[j] // i
    print("Done.", flush=True)

    print("Computing primes using sieve...", flush=True)
    is_prime = np.ones(limit, dtype=bool)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if is_prime[i]:
            is_prime[i*i::i] = False
    print("Done.", flush=True)

    def is_square(x):
        r = int(math.isqrt(x))
        return r * r == x

    # We will find the witness k for each uncovered n
    # such that n - k is prime AND phi(k) * phi(n-k) is a square.
    # To make it super fast, we can pre-identify squares
    max_phi = int(np.max(phi))
    squares = np.zeros(max_phi + 1, dtype=bool)
    for i in range(int(math.isqrt(max_phi)) + 1):
        squares[i*i] = True

    uncovered_without_prime_n_minus_k = []
    
    print("Checking uncovered numbers...", flush=True)
    # We can optimize the check by looping on n
    for n in range(9, 2000001):
        if n % 3 == 0 or n % 10 == 0:
            continue
        
        limit_k = (n - 1) // 2
        found = False
        for k in range(1, limit_k + 1):
            if is_prime[n - k]:
                # Since n-k is prime, phi(n-k) = n-k-1
                prod = int(phi[k]) * (n - k - 1)
                # check if prod is square
                if prod <= max_phi:
                    if squares[prod]:
                        found = True
                        break
                else:
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
