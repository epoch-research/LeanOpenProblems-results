def is_prime_sage(n):
    return n in Primes()

n = 29
M = matrix(ZZ, n, n, lambda i, j: 1 if is_prime_sage((i+1)^2 + (j+1)^2) else 0)
print(f"n=29, det={M.det()}")
