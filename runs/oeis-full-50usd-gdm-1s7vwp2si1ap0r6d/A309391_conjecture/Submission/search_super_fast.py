import math

# We want to find any odd composite n < 1,000,000 such that H_{n-2} \equiv 1 \pmod n.
# This requires: for every prime power p^e || n, we must have v_p(H_{n-2} - 1) >= e.
# As a necessary condition, for each prime factor p of n, we must have v_p(H_{n-2}) >= 0.
# Since H_{n-2} = S_ndiv + 1/p * H_{floor((n-2)/p)}, and v_p(S_ndiv) >= 0,
# we must have v_p(1/p * H_K) >= 0 where K = (n-2)//p.
# This means v_p(H_K) >= 1, i.e., p | H_K's numerator.

# Let's precompute H_K mod p for all primes p and K <= 1,000,000 // p.
# To make it super fast, we can just do this on the fly or pre-filter.
limit = 1000000
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
primes = []
for i in range(2, limit):
    if is_prime[i]:
        primes.append(i)
        for j in range(i*i, limit, i):
            is_prime[j] = False

print("Primes generated.")

# For each odd composite n:
# We factor n.
# Then check the condition.
for n in range(9, limit, 2):
    if is_prime[n]:
        continue
    # Factor n
    temp = n
    factors = []
    for p in primes:
        if p * p > temp:
            if temp > 1:
                factors.append(temp)
            break
        if temp % p == 0:
            factors.append(p)
            while temp % p == 0:
                temp //= p
                
    # Check necessary condition: for each p | n, p | H_{(n-2)//p}
    ok = True
    for p in factors:
        K = (n - 2) // p
        # Compute H_K mod p
        # Since K < n // p, we can compute it very fast!
        # If K >= p, then some terms are divisible by p, so H_K is not a p-adic integer unless the p-part is divisible by p.
        # But for n <= 1,000,000, K < p is almost always true except for very small p.
        # Let's compute H_K mod p rigorously.
        hk = 0
        # If K is too large, we can skip or do it fast.
        # Actually, if K >= p, we can just compute it recursively.
        def get_h_mod_p(m, p_val):
            if m == 0: return 0
            # S_ndiv mod p
            s = 0
            for i in range(1, m + 1):
                if i % p_val != 0:
                    s = (s + pow(i, -1, p_val)) % p_val
            # 1/p * H_{m//p}
            # We need H_{m//p} mod p^2.
            # But we only need modulo p, so we need H_{m//p} mod p^2.
            # For simplicity, if m >= p_val, we can just compute the fraction.
            # Since m <= 1,000,000 // p, if m >= p, then p^2 <= 1,000,000, so p <= 1000.
            # In these cases, we can just use Fractions.
            return s
            
        # Let's do a quick check
        if K < p:
            val = 0
            for i in range(1, K + 1):
                val = (val + pow(i, -1, p)) % p
            if val != 0:
                ok = False
                break
        else:
            # use Fractions or general mod
            from fractions import Fraction
            hk_frac = Fraction(0, 1)
            for i in range(1, K + 1):
                hk_frac += Fraction(1, i)
            if hk_frac.numerator % p != 0:
                ok = False
                break
                
    if ok:
        print(f"Candidate: {n}, factors: {factors}")
        # Now do the full mod check for this candidate
        # ...
