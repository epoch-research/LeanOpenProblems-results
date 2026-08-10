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
            period = GF(b)(2).multiplicative_order()
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
primes_list = list(primes(3, 500))
prime_info = []
for p in primes_list:
    M, R = get_period_and_residues(p)
    if R:
        # Check if R is non-empty
        prime_info.append((p, M, R))

print(f"Collected {len(prime_info)} primes.")

# Let's try to cover all residues of some global LCM L.
# Since we want to cover {5, 6, 7, ...}, let's choose a global LCM L.
# If we choose L to be a multiple of the periods of the primes we use,
# we can check if the union of the covered residues mod L covers all r >= 5 mod L.
# Let's search for a subset of primes that covers everything mod L!
# To do this, we can try to build L by multiplying periods of primes.
# Let's start with L = 6 (prime 7 covers 5). Uncovered mod 6: {0,1,2,3,4}
# For n >= 5, n mod 6 in {0,1,2,3,4} means n can be 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22...
# Let's use a greedy search to find a set of primes and their LCM L.

import heapq

# A state in our search is (uncovered_count, L, uncovered_set, used_primes)
# Since we only care about n >= 5, we can choose a large LCM L,
# and the set of uncovered residues is a subset of {0, 1, ..., L-1}.
# A residue r mod L is "uncovered" if:
# 1) r >= 5 (or there is some n >= 5 with n == r mod L)
# 2) r is not covered by any used prime.
# Note that since L is finite, there is always some n >= 5 with n == r mod L for every r in {0, 1, ..., L-1}.
# So every residue r mod L represents some n >= 5.

# Let's find a covering system!
# We can do this by keeping track of the uncovered set mod L.
# If we add a prime p with period M, the new LCM is L' = lcm(L, M).
# We lift the uncovered set to L', and then remove any residues covered by p.

L = 6
uncovered = {0, 1, 2, 3, 4} # for n >= 5, mod 6 residues {0,1,2,3,4} are not covered by 7
used = [7]

# Let's print out the uncovered residues at each step, and try to find primes that cover them!
# We can find which primes cover which uncovered residues.
# For a prime p with period M and residues R:
# p covers r mod L if there is some u in R such that r == u mod gcd(L, M).
# Let's write a loop to let us interactively or greedily find the best primes!

for step in range(30):
    print(f"\nStep {step}: L = {L}, uncovered count = {len(uncovered)}")
    if len(uncovered) == 0:
        print("SUCCESS! Covered everything!")
        print("Primes:", used)
        break
    if len(uncovered) < 20:
        print("Uncovered residues mod L:", sorted(list(uncovered)))
        
    # Find the best prime to add
    best_p = None
    best_new_uncovered = None
    best_new_L = None
    max_covered_ratio = -1
    
    for p, M, R in prime_info:
        if p in used:
            continue
        new_L = lcm(L, M)
        if new_L > 50000: # limit LCM to 50000
            continue
            
        # Lift uncovered to new_L
        lifted = set()
        for r in uncovered:
            for k in range(new_L // L):
                lifted.add(r + k * L)
                
        # Remove residues covered by p
        # p covers x mod new_L if x % M in R
        covered_by_p = set()
        for x in lifted:
            if (x % M) in R:
                covered_by_p.add(x)
                
        if len(covered_by_p) > 0:
            ratio = len(covered_by_p) / len(lifted)
            if ratio > max_covered_ratio:
                max_covered_ratio = ratio
                best_p = p
                best_new_L = new_L
                best_new_uncovered = lifted - covered_by_p
                
    if best_p is None:
        print("No prime can cover any more residues under LCM limit.")
        break
        
    print(f"Adding prime {best_p} (M={best_new_L}), which covers {max_covered_ratio:.2%} of uncovered.")
    L = best_new_L
    uncovered = best_new_uncovered
    used.append(best_p)
