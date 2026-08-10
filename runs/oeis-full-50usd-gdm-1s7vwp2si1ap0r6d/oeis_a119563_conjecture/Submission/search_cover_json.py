import json
from math import lcm

with open('analyzed_primes.json') as f:
    analyzed = json.load(f)

print(f'Loaded {len(analyzed)} primes.')

# Sort primes by period (smaller periods are better)
analyzed.sort(key=lambda x: x['period'])

# Let's do a greedy search
current_lcm = 6
uncovered = 31 # residues 0, 1, 2, 3, 4 mod 6 are uncovered
used_primes = [7]

step = 0
while step < 100:
    best_p = None
    best_uncovered = None
    best_lcm = None
    best_ratio = 1.0
    
    # To speed up, we can filter candidate primes
    for item in analyzed:
        p = item['prime']
        if p in used_primes:
            continue
        per = item['period']
        res = item['residues']
        
        new_lcm = lcm(current_lcm, per)
        if new_lcm > 1000000: # Limit LCM to 1 million
            continue
            
        # Expand current uncovered
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
    print(f'Step {step}: Added {best_p}, LCM = {current_lcm}, uncovered count = {uncovered_count}, ratio = {best_ratio:.5f}', flush=True)
    if uncovered_count == 0:
        print('FOUND COVERING SYSTEM!!!')
        print('Primes used:', used_primes)
        break
    step += 1
