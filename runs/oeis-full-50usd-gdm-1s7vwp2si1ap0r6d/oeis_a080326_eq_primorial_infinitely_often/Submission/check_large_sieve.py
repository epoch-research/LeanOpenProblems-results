import numpy as np

def solve_up_to(max_n):
    # Sieve to find mobius and primes
    mu = np.ones(max_n + 1, dtype=np.int8)
    square_free = np.ones(max_n + 1, dtype=bool)
    primes = []
    is_prime = np.ones(max_n + 1, dtype=bool)
    is_prime[0] = is_prime[1] = False
    
    for i in range(2, max_n + 1):
        if is_prime[i]:
            primes.append(i)
            for j in range(i, max_n + 1, i):
                is_prime[j] = False
                mu[j] *= -1
            for j in range(i*i, max_n + 1, i*i):
                square_free[j] = False
                mu[j] = 0
                
    # We want to check for each n if it is a solution.
    # a(n) = primorial(n) iff for all primes p <= n,
    # Sum_{m <= n/p, p \nmid m, mu(m)=1, m sq-free} 1/m  \not\equiv 0 (mod p)
    #
    # Let's precompute for each p and each k = n/p:
    # S(k, p) = Sum_{m <= k, p \nmid m, mu(m)=1} 1/m (mod p)
    # Since m <= k < p (if we only care about p > k):
    # If p > k, then p \nmid m is automatically satisfied.
    # So S(k, p) = Sum_{m <= k, mu(m)=1} 1/m (mod p).
    #
    # Let's compute for each k the rational sum:
    # R_k = Sum_{m <= k, mu(m)=1} 1/m
    # Let R_k = A_k / B_k.
    # Then for any prime p > k, S(k, p) \equiv 0 (mod p) iff p divides A_k.
    # This is incredibly simple!
    # A prime p is missing with k = n/p iff p divides A_k (and p > k).
    # Since we need to check all p <= n:
    # - For p <= sqrt(n), i.e., k = n/p >= sqrt(n):
    #   We must explicitly check if Sum_{m <= k, p \nmid m, mu(m)=1} 1/m \equiv 0 (mod p).
    # - For p > sqrt(n), i.e., k = n/p < sqrt(n):
    #   p is missing iff p divides A_k (and p > k).
    
    # Let's compute A_k / B_k for all k up to max_n
    from sympy import Rational
    A = [0] * (max_n + 1)
    B = [0] * (max_n + 1)
    current_sum = Rational(0)
    for k in range(1, max_n + 1):
        if square_free[k] and mu[k] == 1:
            current_sum += Rational(1, k)
        A[k] = current_sum.p
        B[k] = current_sum.q
        
    print("Precomputations done.")
    
    # Now let's check for each n if it is a solution.
    # A prime p <= n is missing if:
    # - if p <= sqrt(n):
    #   We compute S(n/p, p) explicitly with p \nmid m.
    # - if p > sqrt(n):
    #   p divides A_{n/p}
    
    # We can sieve the missing primes!
    # For each k >= 6:
    # Find prime factors of A_k that are > k.
    # Let these be p_1, p_2, ...
    # Then for any n such that n/p = k, i.e., k*p <= n < (k+1)*p,
    # the prime p is missing.
    # So we can just mark all n in [k*p, (k+1)*p) as NOT solutions!
    
    is_sol = np.ones(max_n + 1, dtype=bool)
    is_sol[0] = False
    
    # Small primes check: for p <= sqrt(max_n), we can just explicitly mark
    # those n where S(n/p, p) == 0 (mod p).
    # Since p is small, we can just do this directly.
    import math
    for p in primes:
        if p * p > max_n:
            break
        # We need to check for each n: is S(n/p, p) == 0 (mod p)?
        # Let's compute S(k, p) for all k up to max_n/p
        # S(k, p) = Sum_{m <= k, p \nmid m, mu(m)=1} 1/m (mod p)
        # We can compute this incrementally
        s_val = 0
        # To compute mod p for fractions, we need modular inverse of m mod p.
        # But we only add terms with p \nmid m, so the inverse always exists!
        inv = [0] * p
        for i in range(1, p):
            inv[i] = pow(i, p - 2, p)
            
        S_k = [0] * (max_n // p + 1)
        curr = 0
        for k in range(1, max_n // p + 1):
            if square_free[k] and mu[k] == 1 and k % p != 0:
                curr = (curr + inv[k % p]) % p
            S_k[k] = curr
            
        for k in range(1, max_n // p + 1):
            if S_k[k] == 0:
                # then for all n in [k*p, (k+1)*p), p is missing!
                for n in range(k*p, min((k+1)*p, max_n + 1)):
                    is_sol[n] = False
                    
    print("Small primes checked.")
    
    # Large primes check:
    # For each k >= 6:
    # Find prime factors of A_k that are > k.
    from sympy import primefactors
    for k in range(6, int(max_n / 2) + 1):
        if A[k] == 0:
            continue
        # Find prime factors of A_k that are > k
        for p in primefactors(A[k]):
            if p > k:
                # p is missing for all n in [k*p, (k+1)*p)
                start = k * p
                end = min((k+1)*p, max_n + 1)
                if start < max_n + 1:
                    is_sol[start:end] = False
                    
    print("Large primes checked.")
    
    sols = [i for i in range(1, max_n + 1) if is_sol[i]]
    print("Number of solutions up to", max_n, ":", len(sols))
    print("Largest solutions:", sols[-20:])

solve_up_to(20000)
