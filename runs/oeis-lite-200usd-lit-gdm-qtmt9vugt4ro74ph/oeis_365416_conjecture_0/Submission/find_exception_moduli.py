import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

# Exceptions
exceptions = [11, 23, 29, 83, 113, 131, 167, 173, 185, 227]

# Candidate moduli (any integer >= 3, not necessarily prime, but not dividing 252)
candidates = [M for M in range(3, 100) if 252 % M != 0]

def has_solution_for_val(val, M, p=3):
    # we want to see if there is any f >= 2, e >= 3
    # such that (val^f - p^e - 2) % M == 0.
    # Since f and e are periodic, we can check up to M^2, or just Euler's totient.
    # To be safe, we can just check f in range(2, 100) and e in range(3, 100).
    for f in range(2, 50):
        for e in range(3, 50):
            if (pow(val, f, M) - pow(p, e, M) - 2) % M == 0:
                return True
    return False

# Search for k >= 1
for r in exceptions:
    found_M = None
    for M in candidates:
        all_j_ruled_out = True
        for j in range(M):
            val = (252 * j + r) % M
            if has_solution_for_val(val, M):
                all_j_ruled_out = False
                break
        if all_j_ruled_out:
            found_M = M
            break
    print(f"For k >= 1, r = {r}: ruled out by M = {found_M}")

