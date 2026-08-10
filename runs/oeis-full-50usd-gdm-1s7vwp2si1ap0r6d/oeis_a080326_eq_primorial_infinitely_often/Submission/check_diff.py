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

def find_sols(max_n):
    mu = sieve_mobius(max_n)
    is_sol = np.ones(max_n + 1, dtype=bool)
    is_sol[0] = False
    
    is_prime = np.ones(max_n // 6 + 1, dtype=bool)
    if len(is_prime) > 0:
        is_prime[0] = is_prime[1] = False
    for i in range(2, int((max_n // 6)**0.5) + 1):
        if is_prime[i]:
            for j in range(i*i, max_n // 6 + 1, i):
                is_prime[j] = False
    primes = np.where(is_prime)[0]
    
    for p in primes:
        p = int(p)
        inv = np.zeros(p, dtype=np.int64)
        for x in range(1, p):
            inv[x] = pow(x, p - 2, p)
            
        curr_sum = 0
        limit = max_n // p
        for k in range(1, limit + 1):
            if mu[k] == 1 and k % p != 0:
                curr_sum = (curr_sum + inv[k % p]) % p
            if k >= 6 and curr_sum == 0:
                start = k * p
                end = min((k + 1) * p, max_n + 1)
                is_sol[start:end] = False
                
    sols = np.where(is_sol)[0]
    target_sols = [x for x in sols if 300000 <= x <= 350000]
    print(f"Number of solutions in [228280, 300000]: {len(target_sols)}")
    print(f"Sols: {target_sols[:50]}")

find_sols(350000)
