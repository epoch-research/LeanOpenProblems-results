import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

primes = [p for p in range(2, 1000000) if is_prime(p)]
primes_set = set(primes)

found = []
for p in primes:
    m = p - 2
    if m < 2: continue
    if not is_prime(m):
        # m is composite. Let's find its smallest prime factor
        q = None
        for i in range(2, int(math.sqrt(m)) + 1):
            if m % i == 0:
                q = i
                break
        if q is None: # shouldn't happen for composite
            q = m
        if q >= 107:
            found.append((p, m, q))
            print(f"FOUND: p={p}, p-2={m}, smallest prime factor={q}")
            if len(found) >= 5:
                break

if not found:
    print("NO such primes p exist in the range!")
