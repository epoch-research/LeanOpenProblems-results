import sys
from sympy import isprime, factorint

N = 1048576
N2 = N * N

# Generate all 200 values of v
v_vals = {}
for i in range(20):
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        v = fs * 4**i
        idx = i * 10 + s
        v_vals[idx] = v

blocking_primes = {}
primes_3mod4_small = [p for p in range(3, 100000) if p % 4 == 3 and isprime(p)]

for idx in range(200):
    v = v_vals[idx]
    diff = N2 - v
    if diff == 0:
        print(f"Error! diff is 0 for idx = {idx} (v = {v})")
        sys.exit(1)
        
    abs_diff = abs(diff)
    factors = factorint(abs_diff)
    
    found = False
    for p in sorted(factors.keys()):
        if p % 4 == 3 and factors[p] == 1:
            blocking_primes[idx] = p
            found = True
            break
            
    if not found:
        # Search larger primes if needed
        # We can just factor abs_diff and see if there are larger primes
        for p, exp in factors.items():
            if p % 4 == 3 and exp == 1:
                blocking_primes[idx] = p
                found = True
                break
                
    if not found:
        print(f"Failed to find exact blocking prime for idx = {idx} (v = {v}), factors: {factors}")
        sys.exit(1)

print("SUCCESS! Found exact blocking prime for all 200 indices!")
# Print the dict
print("blocking_primes = {")
for idx in sorted(blocking_primes.keys()):
    print(f"  {idx}: {blocking_primes[idx]},")
print("}")
