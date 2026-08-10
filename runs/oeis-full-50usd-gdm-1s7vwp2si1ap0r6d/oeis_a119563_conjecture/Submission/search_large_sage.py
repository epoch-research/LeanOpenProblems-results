from sage.all import *
import sys

print('Generating primes and computing periods...')
analyzed = []
for p in primes(3, 10000):
    try:
        d = GF(p)(2).multiplicative_order()
    except (ArithmeticError, ValueError):
        continue
    
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
            continue
            
    overall_period = lcm(d, period)
    if overall_period > 50000:
        continue
    
    matching_residues = []
    # Fast check of residues
    start = max(5, a_pow)
    for r in range(start, start + overall_period):
        pow2_r_mod_d = power_mod(2, r, d)
        t1 = power_mod(2, pow2_r_mod_d, p)
        t2 = power_mod(2, r, p)
        if (t1 + t2 - 1) % p == 0:
            matching_residues.append(r % overall_period)
            
    if matching_residues:
        analyzed.append({
            'prime': p,
            'period': int(overall_period),
            'residues': matching_residues
        })

print(f'Collected {len(analyzed)} primes.')

# Greedy search
current_lcm = 6
uncovered = int(31) # residues 0, 1, 2, 3, 4 mod 6 are uncovered
used_primes = [7]

step = 0
while step < 100:
    best_p = None
    best_uncovered = None
    best_lcm = None
    best_ratio = 1.0
    
    for item in analyzed:
        p = item['prime']
        if p in used_primes:
            continue
        per = item['period']
        res = item['residues']
        
        new_lcm = lcm(current_lcm, per)
        if new_lcm > 5000000: # Limit LCM to 5 million
            continue
            
        # Expand current uncovered
        factor = new_lcm // current_lcm
        expanded = uncovered * (((1 << new_lcm) - 1) // ((1 << current_lcm) - 1))
        
        # Apply prime p
        base_mask = ((1 << new_lcm) - 1) // ((1 << per) - 1)
        for r in res:
            mask = base_mask << r
            expanded &= ~mask
            
        ratio = bin(expanded).count('1') / new_lcm
        if ratio < best_ratio:
            best_ratio = ratio
            best_p = p
            best_uncovered = expanded
            best_lcm = new_lcm
            
    if best_p is None:
        print('No prime could be added.')
        break
        
    current_lcm = best_lcm
    uncovered = best_uncovered
    used_primes.append(best_p)
    uncovered_count = bin(uncovered).count('1')
    print(f'Step {step}: Added {best_p}, LCM = {current_lcm}, uncovered count = {uncovered_count}, ratio = {float(best_ratio):.5f}', flush=True)
    if uncovered_count == 0:
        print('FOUND COVERING SYSTEM!!!')
        print('Primes used:', used_primes)
        break
    step += 1
