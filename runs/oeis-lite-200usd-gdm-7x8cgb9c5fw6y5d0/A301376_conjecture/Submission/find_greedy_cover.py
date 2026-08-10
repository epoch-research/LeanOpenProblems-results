import math
from sympy import isprime
from sympy.ntheory.modular import crt

V = [1]
for s in range(5):
    fs = (10 * 16**s + 16 * 4**s + 10) // 9
    for i in range(25):
        val = fs * 4**i
        if val not in V:
            V.append(val)
V.sort()

# Limit U
U = 10**7
target_V = [v for v in V if v < U]
print(f"Number of target V to block: {len(target_V)}")

# Primes p = 3 mod 4
primes = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

def get_qrs(p):
    return sorted(list(set((x*x) % p for x in range(1, p))))

uncovered = set(target_V)
chosen_cover = {}

# We always choose p=3, r=1 because it blocks all powers of 4
chosen_cover[3] = 1
covered_by_3 = set(v for v in uncovered if v % 3 == 1)
uncovered -= covered_by_3
print(f"After p=3, r=1: {len(uncovered)} elements left uncovered.")

for p in primes:
    if p == 3: continue
    if not uncovered: break
    
    # Find residue in QR(p) that covers most uncovered
    best_r = None
    best_covered = set()
    for r in get_qrs(p):
        covered = set(v for v in uncovered if v % p == r)
        if len(covered) > len(best_covered):
            best_covered = covered
            best_r = r
            
    if len(best_covered) > 0:
        chosen_cover[p] = best_r
        uncovered -= best_covered
        print(f"Selected p={p:3d}, r={best_r:3d} (covers {len(best_covered):2d} elements). Uncovered left: {len(uncovered)}")

if not uncovered:
    print("SUCCESS! Full cover found.")
    print("Chosen cover:", chosen_cover)
else:
    print("Failed to cover all. Remaining:", uncovered)
