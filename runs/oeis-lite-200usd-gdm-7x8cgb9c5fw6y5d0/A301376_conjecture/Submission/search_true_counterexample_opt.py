import sys
import math
from sympy import isprime

def is_sum_of_two_squares(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    temp = n
    d = 2
    while d * d <= temp:
        if temp % d == 0:
            count = 0
            while temp % d == 0:
                count += 1
                temp //= d
            if d % 4 == 3 and count % 2 != 0:
                return False
        d += 1
    if temp > 1:
        if temp % 4 == 3:
            return False
    return True

def has_solution(N):
    max_v = int(math.log2(2*N)) + 2
    for v in range(max_v):
        for u in range(v + 1):
            if (2**v - 2**u) % 6 == 0:
                x = (2**v + 2**u) // 2
                y = (2**v - 2**u) // 6
                val = x*x + y*y
                if val <= N*N:
                    k = (u + v) // 2
                    if k <= N:
                        rem = N*N - val
                        if is_sum_of_two_squares(rem):
                            return True
    return False

def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

primes_pool = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

# Search for N which is a multiple of 3
for N in range(3, 100000, 3):
    if N % 1000 == 0:
        print(f"Checking N up to {N}...", flush=True)
        
    if has_solution(N):
        continue
        
    N2 = N * N
    V_all = get_V_all(N2)
    
    # We want to see if we can cover all v in V_all using a small subset of primes
    # Since V_all is sorted, we can do a greedy choice of primes from primes_pool
    uncovered = set(V_all)
    used_primes = []
    
    for p in primes_pool:
        if len(uncovered) == 0:
            break
        # Find if this prime blocks some uncovered elements
        # For a fixed N, N % p^2 is fixed, so the blocking is deterministic
        blocked_by_p = set()
        for v in uncovered:
            diff = N2 - v
            if diff % p == 0 and diff % (p**2) != 0:
                blocked_by_p.add(v)
        if len(blocked_by_p) > 0:
            uncovered -= blocked_by_p
            used_primes.append(p)
            
    if len(uncovered) == 0:
        print(f"\nSUCCESS! Found N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size: {len(V_all)}")
        print(f"V_all: {V_all}")
        print(f"Used primes: {used_primes}")
        res_dict = {p: N % (p**2) for p in used_primes}
        print(f"Residues mod p^2: {res_dict}")
        break
