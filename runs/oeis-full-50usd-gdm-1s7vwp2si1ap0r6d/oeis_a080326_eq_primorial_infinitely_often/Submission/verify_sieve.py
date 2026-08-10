import numpy as np
from sympy import primorial, mobius, Rational

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

def get_sieve_sols(max_n):
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
    return np.where(is_sol)[0]

def a(n):
    total = 0
    for k in range(1, n + 1):
        mu = mobius(k)
        if mu == 1:
            total += Rational(k, 1)
        elif mu == -1:
            total += Rational(1, k)
        else:
            total += 1
    return total.q

exact_sols = []
for n in range(1, 1001):
    if a(n) == primorial(n, nth=False):
        exact_sols.append(n)

sieve_sols = get_sieve_sols(1000)
print("Exact sols:", len(exact_sols), exact_sols[:30])
print("Sieve sols:", len(sieve_sols), list(sieve_sols[:30]))
assert list(exact_sols) == list(sieve_sols)
print("Sieve is 100% correct!")
