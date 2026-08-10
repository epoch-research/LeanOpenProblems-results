import numpy as np
from check_conjecture_super_fast import sieve_mobius, count_solutions

max_n = 1000000
mu = sieve_mobius(max_n)
is_sol = np.ones(max_n + 1, dtype=bool)
is_sol[0] = False
p_limit = max_n // 6
is_prime = np.ones(p_limit + 1, dtype=bool)
if p_limit >= 1:
    is_prime[0] = is_prime[1] = False
for i in range(2, int(p_limit**0.5) + 1):
    if is_prime[i]:
        for j in range(i*i, p_limit + 1, i):
            is_prime[j] = False
primes = np.where(is_prime)[0]

for p in primes:
    p = int(p)
    limit = max_n // p
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
sols_set = set(sols)

# Check for arithmetic progressions A * k + B
# To avoid large B, let's keep A, B small
found = []
for A in range(1, 100):
    for B in range(1, 100):
        # check if A * k + B is in sols_set for all k such that A * k + B <= max_n
        possible = True
        limit_k = (max_n - B) // A
        if limit_k < 10:  # need some decent number of terms
            continue
        for k in range(limit_k + 1):
            if (A * k + B) not in sols_set:
                possible = False
                break
        if possible:
            found.append((A, B))

print("Found APs:", found)
