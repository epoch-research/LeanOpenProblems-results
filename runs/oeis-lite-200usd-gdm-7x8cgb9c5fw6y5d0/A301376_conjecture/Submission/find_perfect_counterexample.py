import math
from sympy import isprime
from sympy.ntheory.modular import crt

def solve():
    # Generate V up to some large limit
    # Since n can be up to 10^100, let's write a function to get all v in V less than a limit X.
    def get_V_up_to(X):
        res = [1]
        for s in range(40):
            fs = (10 * 16**s + 16 * 4**s + 10) // 9
            if fs >= X:
                break
            for i in range(160):
                val = fs * 4**i
                if val >= X:
                    break
                if val not in res:
                    res.append(val)
        res.sort()
        return res

    # We start with a set of primes
    primes = [p for p in range(3, 5000) if isprime(p) and p % 4 == 3]
    
    # We will do a loop:
    # 1. Start with a list of primes we will use. Let's use the first K primes.
    # 2. Find a cover for V up to X = prod_moduli.
    # 3. If we can cover all of them, then we have a candidate n.
    # Let's see:
    K = 1
    while True:
        used_primes = primes[:K]
        # Calculate product of moduli (p^2)
        prod_mod = 1
        for p in used_primes:
            prod_mod *= p**2
            
        # We want to find n <= prod_mod, so n^2 can be up to prod_mod^2.
        # So we need to cover all V up to X = prod_mod^2.
        X = prod_mod**2
        target_V = get_V_up_to(X)
        
        print(f"K = {K}, number of primes: {len(used_primes)}, prod_mod digits: {len(str(prod_mod))}, target V count: {len(target_V)}")
        
        # Let's see if we can cover target_V using used_primes.
        # We can try to find a cover. Since K is fixed, we want to find if there is a choice of residue r_p for each p
        # that covers target_V.
        # Let's write a backtracking or greedy search.
        # To make it exact, let's use backtracking.
        # But wait, is K primes enough to cover target_V?
        # A prime p can cover at most 1/2 of the remaining elements (since only 1/2 of elements mod p are QRs,
        # and we can only choose one QR per prime).
        # So K primes can cover at most a fraction of elements.
        # If target_V is too large, we might not be able to cover it.
        # Let's find the ratio of target_V to K.
        # If K is too small, we increase K.
        # Let's write a search function.
        if len(target_V) > 10 * K:
            # Not enough primes, increase K
            K += 1
            continue
            
        # Try to find a cover using backtracking
        qrs_dict = {}
        for p in used_primes:
            qrs_dict[p] = sorted(list(set((x*x) % p for x in range(1, p))))
            
        solution = {}
        uncovered = set(target_V)
        
        # Backtracking search
        def search(idx, current_uncovered):
            if not current_uncovered:
                return True
            if idx == len(used_primes):
                return False
                
            p = used_primes[idx]
            # Try to choose r from qrs_dict[p]
            # To optimize, we sort r by how many elements they cover
            candidates = []
            for r in qrs_dict[p]:
                cov = [v for v in current_uncovered if v % p == r]
                if cov:
                    candidates.append((len(cov), r, cov))
            candidates.sort(reverse=True)
            
            # Also we must choose a residue even if it covers 0 elements?
            # Actually, yes, because we must choose some residue mod p^2 for every prime.
            # If no candidate covers anything, we can just choose any QR, e.g., candidates.append((0, qrs_dict[p][0], []))
            if not candidates:
                candidates.append((0, qrs_dict[p][0], []))
                
            for _, r, cov in candidates:
                solution[p] = r
                if search(idx + 1, current_uncovered - set(cov)):
                    return True
                del solution[p]
            return False
            
        if search(0, uncovered):
            print("FOUND PERFECT COVER!")
            print("Solution:", solution)
            break
        else:
            print("Failed to cover. Increasing K.")
            K += 1

solve()
