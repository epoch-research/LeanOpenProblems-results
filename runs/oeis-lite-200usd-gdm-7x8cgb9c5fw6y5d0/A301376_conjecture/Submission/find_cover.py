import math
from sympy import factorint
from sympy.ntheory.modular import crt

# Generate V
V = [1]
for s in range(5):
    fs = (10 * 16**s + 16 * 4**s + 10) // 9
    for i in range(25):
        val = fs * 4**i
        if val not in V:
            V.append(val)
V.sort()

# Primes to use (all congruent to 3 mod 4)
primes = [3, 7, 11, 19, 23, 31, 43, 47, 59]

# For each prime, the possible quadratic residues (including 0 if we want, but non-zero is safer)
def get_qrs(p):
    return sorted(list(set((x*x) % p for x in range(1, p))))

qrs_dict = {p: get_qrs(p) for p in primes}

# We want to choose a residue r_p for each p in primes
# Let's do a backtracking search to find a combination of residues
# that blocks as many elements of V as possible.
# An element v is blocked by (p, r_p) if v % p == r_p.

# Let's restrict to V elements up to some limit, say 500000.
# If we can block all of them, the candidate n (which will be around prod(p^2) approx 10^21)
# will have n^2 - v blocked for all v < 500000.
# What about v >= 500000? There are very few of them up to n^2!
# Actually, let's see if we can find a combination that blocks the first K elements of V.

K = 35  # block first 35 elements of V
target_V = V[:K]
print("Target V to block:", target_V)

def solve_cover(prime_idx, current_residues):
    if prime_idx == len(primes):
        # Check how many of target_V are blocked
        blocked = []
        for v in target_V:
            is_blocked = False
            for p, r in current_residues.items():
                if v % p == r:
                    is_blocked = True
                    break
            if is_blocked:
                blocked.append(v)
        if len(blocked) == len(target_V):
            return current_residues
        return None
        
    p = primes[prime_idx]
    # To speed up, we can try residues that block at least some uncovered elements
    for r in qrs_dict[p]:
        current_residues[p] = r
        res = solve_cover(prime_idx + 1, current_residues)
        if res is not None:
            return res
        del current_residues[p]
    return None

sol = solve_cover(0, {})
print("Solution residues:", sol)
