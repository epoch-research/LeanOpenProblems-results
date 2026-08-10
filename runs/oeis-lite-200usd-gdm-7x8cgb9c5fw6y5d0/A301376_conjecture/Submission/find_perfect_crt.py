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

    # We want to choose a counterexample n
    # Let's set up the initial moduli and residues:
    # 1. n^2 = 1 mod 9 (or n = 1 mod 9, which implies n^2 = 1 mod 9)
    # 2. n^2 = 8 mod 49 (which implies n = 13 mod 49 or 36 mod 49, both of which give n^2 = 169 = 22 mod 49?
    #    Wait! 13^2 = 169 = 22 mod 49. 15^2 = 225 = 29 mod 49.
    #    Let's find x mod 49 such that x^2 = 8 mod 49?
    #    Does 8 have a square root mod 49?
    #    Legendre(8, 7) = Legendre(2, 7) = 1. Yes, 8 is a QR mod 7.
    #    Let's find square roots of 8 mod 49:
    roots_8_mod_49 = [x for x in range(49) if (x*x) % 49 == 8]
    print("Roots of 8 mod 49:", roots_8_mod_49) # [15, 34]
    
    # So we can choose moduli and residues:
    # We will use 9 (residue 1) and 49 (residue 15).
    # Since gcd(9, 49) = 1, we can do this.
    # This blocks almost all powers of 4!
    
    # Let's list the other elements of V we need to block.
    # Suppose we want to block all elements of V up to some limit U = 10^6.
    U = 10**6
    target_V = [v for v in V if v < U]
    
    # Let's see which elements of target_V are already blocked by 9 and 49:
    blocked_by_9_49 = []
    for v in target_V:
        # Check if 3 or 7 blocks v
        # For 3: we need (n^2 - v) % 9 in {3, 6}, which means (1 - v) % 9 in {3, 6}
        # For 7: we need (n^2 - v) % 49 to be a multiple of 7 but not 49
        # since n^2 = 8 mod 49, we need (8 - v) % 49 to be in {7, 14, 21, 28, 35, 42}
        if (1 - v) % 9 in {3, 6}:
            blocked_by_9_49.append(v)
        elif (8 - v) % 49 in {7, 14, 21, 28, 35, 42}:
            blocked_by_9_49.append(v)
            
    uncovered = set(target_V) - set(blocked_by_9_49)
    print("Uncovered elements of V:", sorted(list(uncovered)))
    
    # We can use other primes p = 3 mod 4 to cover the remaining uncovered elements!
    primes = [p for p in range(11, 1000) if isprime(p) and p % 4 == 3]
    
    def get_qrs(p):
        return sorted(list(set((x*x) % p for x in range(1, p))))
        
    chosen_cover = {}
    for p in primes:
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
        print("Failed to cover all. Remaining:", uncovered)
        return
        
    print("Chosen extra cover:", chosen_cover)
    
    # Solve CRT
    moduli = [9, 49]
    residues = [1, 15] # n = 1 mod 9, n = 15 mod 49
    
    for p, r in chosen_cover.items():
        moduli.append(p**2)
        # find root mod p
        root = -1
        for x in range(p):
            if (x*x) % p == r % p:
                root = x
                break
        # lift mod p^2
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
    
    # Check if n is a counterexample
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
