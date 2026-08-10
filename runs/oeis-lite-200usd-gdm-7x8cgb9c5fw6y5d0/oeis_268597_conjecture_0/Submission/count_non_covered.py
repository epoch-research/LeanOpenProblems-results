import sympy

def check_m(m):
    if sympy.isprime(m):
        return True
    factors = sympy.factorint(m)
    # Case 1: Prime power
    if len(factors) == 1:
        return True
    # Case 2: 2^k * q^a (q >= 3)
    if len(factors) == 2 and 2 in factors:
        return True
    # Case 3: 2^k * 3^j * q^a (q >= 5)
    if len(factors) == 3 and 2 in factors and 3 in factors:
        return True
    # Case 4: 2^k * 3^j
    if len(factors) == 2 and 2 in factors and 3 in factors:
        return True
    return False

non_covered = []
for m in range(501, 10000):
    if not check_m(m):
        non_covered.append(m)

print(f"Total non-covered composite m up to 10000: {len(non_covered)}")
print(f"First 100 non-covered: {non_covered[:100]}")
