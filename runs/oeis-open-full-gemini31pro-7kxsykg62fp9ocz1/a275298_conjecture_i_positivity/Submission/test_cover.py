import sys

def solve():
    primes = [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199]
    
    # We want to greedily pick c_i for each p_i to cover the maximum number of remaining (w, v) mod M.
    # Since we can't maintain the full grid for large M, let's just do a small test.
    # Let's take the first few primes and see if we can cover a large fraction.
    import random
    
    # To check if full cover is possible, we can use a randomized greedy approach on a subset of (w, v)
    # Actually, we can just represent the "uncovered" density.
    
    # For independent choices, the uncovered density would be prod(1 - D_i)
    # D_i = fraction of pairs covered by prime p_i.
    # D_i is roughly (p-1)/p^2 if we pick the best c_i.
    
    # Is it exactly (p-1)/p^2 ? Let's check for p=3.
    # f(w, v) = w^3 + (w+v^2)^2
    def f(w, v):
        return w**3 + (w + v**2)**2
        
    for p in primes[:5]:
        counts = {}
        for w in range(p**2):
            for v in range(p**2):
                val = f(w, v) % (p**2)
                counts[val] = counts.get(val, 0) + 1
        
        # For a choice of n_mod_p2 = c, we cover those (w, v) where f(w,v) % p == c % p and f(w,v) % p^2 != c
        best_c = 0
        best_cov = 0
        for c in range(p**2):
            cov = 0
            for val, count in counts.items():
                if val % p == c % p and val != c:
                    cov += count
            if cov > best_cov:
                best_cov = cov
                best_c = c
        print(f"p={p}, best cover: {best_cov} out of {p**4} (fraction {best_cov/p**4:.4f}), (p-1)/p^2 = {(p-1)/p**2:.4f}")

solve()
