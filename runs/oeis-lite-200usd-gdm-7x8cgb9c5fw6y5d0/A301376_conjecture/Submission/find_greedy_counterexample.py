import math
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

def solve():
    V = [1]
    for s in range(5):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(25):
            val = fs * 4**i
            if val not in V:
                V.append(val)
    V.sort()

    U = 10**5
    target_V = [v for v in V if v < U]
    print(f"Number of target V to block: {len(target_V)}")

    primes = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

    def get_qrs(p):
        return sorted(list(set((x*x) % p for x in range(1, p))))

    uncovered = set(target_V)
    chosen_cover = {}

    chosen_cover[3] = 1
    uncovered -= set(v for v in uncovered if v % 3 == 1)

    for p in primes:
        if p == 3: continue
        if not uncovered: break
        
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

    if uncovered:
        print("Failed to cover all under U. Remaining:", uncovered)
        return

    print("Greedy cover found:", chosen_cover)
    
    moduli = []
    residues = []
    for p, r in chosen_cover.items():
        moduli.append(p**2)
        root = -1
        for x in range(p):
            if (x*x) % p == r % p:
                root = x
                break
        lift = -1
        for k in range(p):
            x = root + k*p
            if (x*x - r) % (p**2) != 0:
                lift = x
                break
        residues.append(lift)
        
    n, prod = crt(moduli, residues)
    n = int(n)
    prod = int(prod)
    if n % 2 == 0:
        n += prod
        
    print(f"Candidate n = {n}")
    print(f"Number of digits: {len(str(n))}")
    
    def is_sum_of_two_squares_fast(m):
        if m < 0: return False
        if m == 0 or m == 1: return True
        factors = factorint(m)
        for p, e in factors.items():
            if p % 4 == 3 and e % 2 != 0:
                return False
        return True

    is_counter = True
    failing_v = None
    for v in V:
        if v >= n*n: break
        if is_sum_of_two_squares_fast(n*n - v):
            is_counter = False
            failing_v = v
            break
            
    if is_counter:
        print(f"SUCCESS! COUNTEREXAMPLE FOUND: n = {n}")
    else:
        print(f"Failed because of v = {failing_v}")

solve()
