import sys
from sympy import isprime

def get_V_all(N2):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= N2:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= N2:
                break
            V.add(val)
    return sorted(list(V))

primes_3mod4_limit = [p for p in range(3, 5000) if p % 4 == 3 and isprime(p)]

print(f"Starting fast search with {len(primes_3mod4_limit)} primes congruent to 3 mod 4 up to 5000...")
sys.stdout.flush()

for N in range(10000, 10000000):
    if N % 100000 == 0:
        print(f"Checked up to N = {N}")
        sys.stdout.flush()
        
    N2 = N * N
    V_all = get_V_all(N2)
    
    all_blocked_by_small = True
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        if diff == 0:
            all_blocked_by_small = False
            break
            
        found = False
        for p in primes_3mod4_limit:
            if diff % p == 0 and diff % (p*p) != 0:
                blocking_primes[v] = p
                found = True
                break
        if not found:
            all_blocked_by_small = False
            break
            
    if all_blocked_by_small:
        print(f"\nFOUND EASY COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size: {len(V_all)}")
        print(f"blocking_primes = {blocking_primes}")
        sys.exit(0)

print("No easy counterexample found up to 10,000,000.")
