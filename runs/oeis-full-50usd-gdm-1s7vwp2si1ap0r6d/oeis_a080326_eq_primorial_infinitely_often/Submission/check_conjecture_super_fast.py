import time
import numpy as np

def sieve_mobius(n):
    mu = np.ones(n + 1, dtype=np.int8)
    is_prime = np.ones(n + 1, dtype=bool)
    is_prime[0] = is_prime[1] = False
    for i in range(2, n + 1):
        if is_prime[i]:
            for j in range(i, n + 1, i):
                is_prime[j] = False
                mu[j] *= -1
            i2 = i * i
            for j in range(i2, n + 1, i2):
                mu[j] = 0
    return mu

def count_solutions(max_n):
    t0 = time.time()
    mu = sieve_mobius(max_n)
    
    is_sol = np.ones(max_n + 1, dtype=bool)
    is_sol[0] = False
    
    # Simple sieve to get primes up to max_n // 6
    p_limit = max_n // 6
    is_prime = np.ones(p_limit + 1, dtype=bool)
    if p_limit >= 1:
        is_prime[0] = is_prime[1] = False
    for i in range(2, int(p_limit**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, p_limit + 1, i):
                is_prime[j] = False
    primes = np.where(is_prime)[0]
    
    print(f"Sieve done. Primes count: {len(primes)}")
    
    for p in primes:
        p = int(p)
        limit = max_n // p
        
        # Only compute inverses for needed values (at most limit)
        # We can compute inverses on demand and cache them
        inv = {}
        
        curr_sum = 0
        for k in range(1, limit + 1):
            if mu[k] == 1 and k % p != 0:
                rem = k % p
                if rem not in inv:
                    inv[rem] = pow(rem, p - 2, p)
                curr_sum = (curr_sum + inv[rem]) % p
            if k >= 6 and curr_sum == 0:
                start = k * p
                end = min((k + 1) * p, max_n + 1)
                is_sol[start:end] = False
                
    sols = np.where(is_sol)[0]
    t1 = time.time()
    print(f"Total solutions up to {max_n}: {len(sols)} in {t1-t0:.2f} seconds")
    print(f"Largest 20 solutions: {sols[-20:]}")

count_solutions(1000000)
count_solutions(5000000)
count_solutions(10000000)
