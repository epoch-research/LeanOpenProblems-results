import math

# Fast totient using a sieve for precomputation
limit = 2000005
phi = list(range(limit))
for i in range(2, limit):
    if phi[i] == i: # i is prime
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

print("Sieve done. Searching for counterexamples...")

# Let's check all n from 9 to 2,000,000
for n in range(9, 2000000 + 1):
    found = False
    # Check if we have an algebraic rule first (which guarantees a(n) > 0)
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    
    # Otherwise search for witness k
    for k in range(1, (n - 1) // 2 + 1):
        if is_square(phi[k] * phi[n - k]):
            found = True
            break
    if not found:
        print(f"COUNTEREXAMPLE FOUND: n = {n}")
        break
else:
    print("No counterexample found in the range.")
