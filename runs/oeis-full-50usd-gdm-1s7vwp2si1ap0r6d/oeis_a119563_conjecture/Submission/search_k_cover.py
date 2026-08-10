from sage.all import *

print('Searching for a covering system in terms of k...')
analyzed = []
for p in primes(3, 1000):
    try:
        d = GF(p)(2).multiplicative_order()
    except:
        continue
    
    # period of 2^(32k) mod p
    # which is d_1 = d / gcd(32, d)
    d_1 = d // gcd(32, d)
    
    overall_period = d_1 * p
    if overall_period > 100000:
        continue
        
    matching_residues = []
    for r in range(overall_period):
        t1 = power_mod(2, 32 * r, p)
        t2 = (32 * r) % p
        if (t1 + t2 - 1) % p == 0:
            matching_residues.append(r)
            
    if matching_residues:
        analyzed.append({
            'prime': int(p),
            'period': int(overall_period),
            'residues': [int(r) for r in matching_residues]
        })

print(f'Collected {len(analyzed)} primes.')

# Greedy search to cover all k >= 1
# Since we want to cover all residues modulo some LCM,
# let's start with L = 3 and uncovered = {1, 2} (since 0 is covered by p=3)
L = 3
uncovered = {1, 2}
used = [3]

for step in range(50):
    if len(uncovered) == 0:
        print('SUCCESS! Covered everything!')
        print('Primes:', used)
        break
        
    best_p = None
    best_new_L = None
    best_uncovered = None
    max_covered = -1
    
    for item in analyzed:
        p = item['prime']
        if p in used:
            continue
        M = item['period']
        R = item['residues']
        
        new_L = lcm(L, M)
        if new_L > 2000000: # Limit LCM to 2 million
            continue
            
        factor = new_L // L
        lifted = {u + j * L for u in uncovered for j in range(factor)}
        
        covered_by_p = {x for x in lifted if (x % M) in R}
        
        if len(covered_by_p) > max_covered:
            max_covered = len(covered_by_p)
            best_p = p
            best_new_L = new_L
            best_uncovered = lifted - covered_by_p
            
    if best_p is None or max_covered <= 0:
        print(f'No prime could be added. L={L}, uncovered={len(uncovered)}')
        break
        
    print(f'Step {step}: Added {best_p}, LCM = {best_new_L}, covered = {max_covered}, remaining = {len(best_uncovered)}')
    L = best_new_L
    uncovered = best_uncovered
    used.append(best_p)
