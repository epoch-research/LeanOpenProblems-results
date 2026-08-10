import sympy

def phi(n):
    return sympy.totient(n)

# Let's test different candidate formulas for composite m = n + 1.
# We want (x - 1) % phi(x) == n, which is equivalent to:
# x - 1 = k * phi(x) + m - 1
# i.e., x - m = k * phi(x).
# Since m is composite, it has a prime factor p. Let m = p * B.
# Can we choose x as a function of p and B?
# Let's test for all composite m:
# 1) x = p * m?
# 2) x = p^2 * B?
# 3) x = p * B^2?
# 4) x = p^2 * B^2?
# Let's see if any of these (or other simple combinations) satisfy x - m = k * phi(x) or (x-1)%phi(x) == n.

for m in range(4, 500):
    if not sympy.isprime(m):
        n = m - 1
        # Let's find all prime factors of m
        factors = sympy.factorint(m)
        p = min(factors.keys()) # smallest prime factor
        B = m // p
        
        # Test 1: x = p * m = p^2 * B
        x1 = p * m
        # Test 2: x = p^2 * B? That's the same as p * m.
        # Test 3: x = p * B^2?
        x3 = p * B * B
        # Test 4: x = (p+1) * B?
        # Test 5: x = p^2 * (B + 1)?
        # Let's search over x of the form p^a * B^b * (some small factor)
        found = False
        for a in [1, 2, 3]:
            for b in [1, 2, 3]:
                for c in [1, 2, 3, p, p-1, p+1, B, B-1, B+1]:
                    x = p**a * B**b * c
                    if x > 0 and (x - 1) % phi(x) == n:
                        # print(f"m={m}, p={p}, B={B}, x = p^{a} * B^{b} * {c} works! phi(x)={phi(x)}")
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if not found:
            print(f"No simple x found for m={m}")
