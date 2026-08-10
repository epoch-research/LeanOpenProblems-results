import math
from sympy import factorint

# We want to find a list of values of v.
V = [1]
for s in range(5):
    fs = (10 * 16**s + 16 * 4**s + 10) // 9
    for i in range(20):
        val = fs * 4**i
        if val not in V:
            V.append(val)
V.sort()

# Check if m is a sum of two squares using sympy's factorint
def is_sum_of_two_squares_fast(m):
    if m < 0: return False
    if m == 0 or m == 1: return True
    factors = factorint(m)
    for p, e in factors.items():
        if p % 4 == 3 and e % 2 != 0:
            return False
    return True

# Solve CRT
def ext_gcd(a, b):
    if b == 0: return (1, 0, a)
    x1, y1, g = ext_gcd(b, a % b)
    return (y1, x1 - (a // b) * y1, g)

def mod_inv(a, m):
    x, y, g = ext_gcd(a, m)
    if g != 1: return None
    return x % m

def crt(residues, moduli):
    N = 1
    for m in moduli: N *= m
    x = 0
    for r, m in zip(residues, moduli):
        Ni = N // m
        inv = mod_inv(Ni, m)
        if inv is None: return None
        x = (x + r * inv * Ni) % N
    return x

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0: return False
    return True

def legendre(a, p):
    return pow(a, (p - 1) // 2, p)

def find_primes(M):
    primes_list = []
    used = set()
    for j in range(M):
        v = V[j]
        found = False
        is_sq = (int(math.isqrt(v))**2 == v)
        for p in range(3, 5000):
            if is_prime(p) and p % 4 == 3 and p not in used:
                if is_sq or legendre(v, p) == 1:
                    used.add(p)
                    primes_list.append((v, p))
                    found = True
                    break
        if not found:
            return None
    return primes_list

# Let's search candidates for different M
for M in range(2, 15):
    primes_list = find_primes(M)
    if primes_list is None: continue
    
    moduli = [p**2 for v, p in primes_list]
    residues = []
    for v, p in primes_list:
        r = -1
        for x in range(p):
            if (x*x) % p == v % p:
                r = x
                break
        valid_lifts = []
        for k in range(p):
            x = r + k*p
            if (x*x - v) % (p**2) != 0:
                valid_lifts.append(x)
        residues.append(valid_lifts[0])
        
    n = crt(residues, moduli)
    prod_mod = 1
    for m in moduli: prod_mod *= m
    if n % 2 == 0:
        n += prod_mod
        
    print(f"M={M}: Candidate n = {n} (digits: {len(str(n))})")
    # Check if n is a counterexample
    is_counter = True
    failing_v = None
    for v in V:
        if v >= n*n: break
        if is_sum_of_two_squares_fast(n*n - v):
            is_counter = False
            failing_v = v
            break
    if is_counter:
        print(f"SUCCESS! COUNTEREXAMPLE FOUND: n = {n}")
        break
    else:
        print(f"Failed because of v = {failing_v}")
