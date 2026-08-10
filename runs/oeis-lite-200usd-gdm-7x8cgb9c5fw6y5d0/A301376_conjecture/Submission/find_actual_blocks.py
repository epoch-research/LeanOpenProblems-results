import sys
from sympy import isprime

n = 126686524250410004736537312064293613795653657092983804510554503324715379258723493119883344012301288982405926046569374575432235100014312858069895494644651006289334684761526421296266808332923548185778355634967387614240536269449875614849275
n2 = n*n

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

V_all = get_V_all(n2)
print(f"Total V_all size: {len(V_all)}")

# Precompute primes congruent to 3 mod 4 up to 1,000,000
print("Precomputing primes...")
primes_3mod4 = [p for p in range(3, 1000000) if isprime(p) and p % 4 == 3]
print(f"Precomputed {len(primes_3mod4)} primes.")

v_to_prime = {}
unblocked = []

for idx, v in enumerate(V_all):
    val = n2 - v
    found = False
    for p in primes_3mod4:
        if val % p == 0:
            # Check if exponent is odd
            count = 0
            temp = val
            while temp % p == 0:
                count += 1
                temp //= p
            if count % 2 != 0:
                v_to_prime[v] = p
                found = True
                break
    if not found:
        unblocked.append(v)
    if idx % 500 == 0:
        print(f"Processed {idx} / {len(V_all)}")

if unblocked:
    print(f"FAILED! {len(unblocked)} elements are not blocked by any prime < 1,000,000.")
    print("First few unblocked:", unblocked[:10])
else:
    print("SUCCESS! All elements in V_all are blocked.")
    # Print the unique primes we used
    unique_primes = sorted(list(set(v_to_prime.values())))
    print(f"Number of unique primes used: {len(unique_primes)}")
    print(f"Primes used: {unique_primes}")
