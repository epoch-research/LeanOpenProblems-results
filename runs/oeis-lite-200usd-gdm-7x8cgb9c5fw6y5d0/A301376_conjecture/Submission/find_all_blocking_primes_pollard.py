import sys
import time
from sympy import isprime
from sympy.ntheory.factor_ import pollard_rho

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()

N = 1161740213061274220886037
N2 = N * N

# Filter V_all < N2
V_all = [v for v in all_V_precomputed if v < N2]
print(f"N = {N}")
print(f"V_all size: {len(V_all)}")
sys.stdout.flush()

# Small primes up to 1,000
small_primes = []
for p in range(2, 1000):
    if isprime(p):
        small_primes.append(p)

# A recursive function to find a prime factor congruent to 3 mod 4 with odd exponent
def find_blocking_prime_recursive(n):
    if n <= 1:
        return None
    if isprime(n):
        if n % 4 == 3:
            return n
        return None
        
    # If not prime, find a factor using pollard_rho
    d = pollard_rho(n)
    if d is None or d == n or d == 1:
        # Fall back to trial division or return None
        for p in range(2, 100000):
            if n % p == 0:
                d = p
                break
        if d is None or d == n or d == 1:
            return None
            
    # Check if we can find a blocking prime in d or n // d
    # But wait, we must be careful with exponents!
    # If a prime factor has an even exponent, it does not block.
    # To be mathematically rigorous, we should just fully factor n using a quick pollard-rho based factorizer
    # and then check the prime factors and their exponents.
    return None

def quick_factor(n):
    factors = {}
    
    # Trial division first for very small primes
    for p in small_primes:
        if p * p > n:
            break
        if n % p == 0:
            exp = 0
            while n % p == 0:
                n //= p
                exp += 1
            factors[p] = exp
            
    # Helper recursive factorizer
    def rec_factor(m):
        if m <= 1:
            return
        if isprime(m):
            factors[m] = factors.get(m, 0) + 1
            return
        d = pollard_rho(m)
        if d is None or d == m or d == 1:
            # Fallback trial division
            found = False
            for p in range(2, 100000):
                if m % p == 0:
                    rec_factor(p)
                    rec_factor(m // p)
                    found = True
                    break
            if not found:
                # If we still can't factor it, just treat m as a prime factor (with warning)
                print(f"Warning: could not factor {m}")
                factors[m] = factors.get(m, 0) + 1
            return
        rec_factor(d)
        rec_factor(m // d)

    rec_factor(n)
    return factors

blocking_primes = {}
unblocked = []

start_time = time.time()
for idx, v in enumerate(V_all):
    if idx % 200 == 0:
        print(f"Processed {idx} elements in {time.time() - start_time:.2f}s...", flush=True)
    diff = N2 - v
    
    factors = quick_factor(diff)
    
    found_p = None
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            found_p = p
            break
            
    if found_p is not None:
        blocking_primes[v] = found_p
    else:
        unblocked.append((v, factors))

print(f"Time taken to check all: {time.time() - start_time:.2f}s")
print(f"Unblocked elements: {len(unblocked)}")
if len(unblocked) == 0:
    print("SUCCESS! All elements are blocked!")
    primes_used = set(blocking_primes.values())
    print(f"Distinct blocking primes used: {len(primes_used)}")
    print(f"Max blocking prime: {max(primes_used)}")
    print(f"Min blocking prime: {min(primes_used)}")
    
    with open("/workspace/leanproject/Submission/success_25digit.py", "w") as f:
        f.write(f"N = {N}\n")
        f.write(f"blocking_primes = {blocking_primes}\n")
else:
    print("Unblocked elements and their factors:")
    for v, factors in unblocked[:10]:
        print(f"v = {v}: factors = {factors}")
