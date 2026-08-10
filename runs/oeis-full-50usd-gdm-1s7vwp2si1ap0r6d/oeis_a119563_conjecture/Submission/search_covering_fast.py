from sage.all import *

def get_period_and_residues(p):
    try:
        d = GF(p)(2).multiplicative_order()
    except (ArithmeticError, ValueError):
        return None, []
    
    b = d
    a_pow = 0
    while b % 2 == 0:
        b //= 2
        a_pow += 1
    
    if b == 1:
        period = 1
    else:
        try:
            period = IntegerModRing(b)(2).multiplicative_order()
        except (ArithmeticError, ValueError):
            return None, []
            
    overall_period = lcm(d, period)
    
    matching_residues = []
    start = max(5, a_pow)
    for r in range(start, start + overall_period):
        pow2_r_mod_d = power_mod(2, r, d)
        t1 = power_mod(2, pow2_r_mod_d, p)
        t2 = power_mod(2, r, p)
        if (t1 + t2 - 1) % p == 0:
            matching_residues.append(r % overall_period)
            
    return overall_period, matching_residues

# Collect useful primes and their covered residues
primes_list = list(primes(3, 1000))
prime_info = []
for p in primes_list:
    M, R = get_period_and_residues(p)
    if R and M <= 1000:
        prime_info.append((p, M, R))

print(f"Collected {len(prime_info)} primes.")

# Let's do a fast greedy search using a set of uncovered residues modulo a large LCM L.
# Since L can be up to 10,000,000, let's keep a set of uncovered residues.
# If we start with L = 6 and uncovered = {0,1,2,3,4}.
# At each step, we find the prime p that covers the most uncovered residues when lifted to the new LCM.

L = 6
uncovered = {0, 1, 2, 3, 4}
used = [7]

for step in range(50):
    if len(uncovered) == 0:
        print("SUCCESS! Covered everything!")
        print("Primes:", used)
        break
    print(f"Step {step}: L={L}, uncovered={len(uncovered)}", flush=True)
    
    best_p = None
    best_new_L = None
    best_uncovered = None
    max_covered = -1
    
    for p, M, R in prime_info:
        if p in used:
            continue
        new_L = lcm(L, M)
        if new_L > 2000000: # Limit LCM to 2 million
            continue
            
        # Lift uncovered to new_L
        factor = new_L // L
        lifted = {u + k * L for u in uncovered for k in range(factor)}
        
        # Check which are covered by p
        covered_by_p = {x for x in lifted if (x % M) in R}
        
        if len(covered_by_p) > max_covered:
            max_covered = len(covered_by_p)
            best_p = p
            best_new_L = new_L
            best_uncovered = lifted - covered_by_p
            
    if best_p is None or max_covered <= 0:
        print("No prime can cover any more residues.")
        break
        
    print(f"  Adding prime {best_p}, LCM={best_new_L}, covered={max_covered}", flush=True)
    L = best_new_L
    uncovered = best_uncovered
    used.append(best_p)
