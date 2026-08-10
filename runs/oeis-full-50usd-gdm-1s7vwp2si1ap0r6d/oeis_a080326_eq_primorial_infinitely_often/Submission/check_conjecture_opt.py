from sympy import primerange, mobius
import time

def count_solutions(max_n):
    t0 = time.time()
    # Precompute mobius
    mu = [0] * (max_n + 1)
    for i in range(1, max_n + 1):
        mu[i] = mobius(i)
        
    is_sol = [True] * (max_n + 1)
    is_sol[0] = False
    
    primes = list(primerange(2, max_n // 6 + 1))
    
    for p in primes:
        # Precompute mod p inverses
        inv = [0] * p
        for x in range(1, p):
            inv[x] = pow(x, p - 2, p)
            
        curr_sum = 0
        limit = max_n // p
        for k in range(1, limit + 1):
            if mu[k] == 1 and k % p != 0:
                curr_sum = (curr_sum + inv[k % p]) % p
            if k >= 6 and curr_sum == 0:
                # Mark all n in [k*p, (k+1)*p) as False
                start = k * p
                end = min((k + 1) * p, max_n + 1)
                for n in range(start, end):
                    is_sol[n] = False
                    
    sols = [i for i, val in enumerate(is_sol) if val]
    t1 = time.time()
    print(f"Total solutions up to {max_n}: {len(sols)} in {t1-t0:.2f} seconds")
    print(f"Largest 20 solutions: {sols[-20:]}")

count_solutions(1000000)
