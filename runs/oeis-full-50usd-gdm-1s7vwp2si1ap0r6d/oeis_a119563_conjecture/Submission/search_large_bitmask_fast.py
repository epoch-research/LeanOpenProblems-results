import json
from math import lcm, gcd

with open('analyzed_primes.json') as f:
    analyzed = json.load(f)

print(f'Loaded {len(analyzed)} primes.')

# Sort primes by period
analyzed.sort(key=lambda x: x['period'])

current_lcm = 6
uncovered = 31 # residues 0,1,2,3,4 mod 6
used_primes = [7]

step = 0
while step < 100:
    uncovered_count = bin(uncovered).count('1')
    if uncovered_count == 0:
        print('FOUND COVERING SYSTEM!!!')
        print('Primes used:', used_primes)
        break
        
    # 1. Apply any prime whose period divides current_lcm and covers at least one residue
    applied_divisor_prime = False
    for item in analyzed:
        p = item['prime']
        if p in used_primes:
            continue
        per = item['period']
        if current_lcm % per == 0:
            # Check if it covers anything
            res = item['residues']
            base_mask = ((1 << current_lcm) - 1) // ((1 << per) - 1)
            covered_mask = 0
            for r in res:
                covered_mask |= base_mask << r
            
            if (uncovered & covered_mask) != 0:
                uncovered &= ~covered_mask
                used_primes.append(p)
                new_count = bin(uncovered).count('1')
                print(f'Step {step} (Divisor): Added {p}, LCM = {current_lcm}, uncovered = {new_count}', flush=True)
                applied_divisor_prime = True
                break
                
    if applied_divisor_prime:
        step += 1
        continue
        
    # 2. If no divisor prime covers anything, find the best prime that increases LCM
    best_p = None
    best_uncovered = None
    best_lcm = None
    best_ratio = 1.0
    
    # We restrict candidates to primes that don't increase LCM too much
    # and we prioritize smaller LCMs
    candidates = []
    for item in analyzed:
        p = item['prime']
        if p in used_primes:
            continue
        per = item['period']
        new_lcm = lcm(current_lcm, per)
        if new_lcm > 50000000: # Limit LCM to 50 million
            continue
        candidates.append((new_lcm, p, item))
        
    # Sort candidates by new_lcm so we check smaller LCMs first
    candidates.sort(key=lambda x: x[0])
    
    for new_lcm, p, item in candidates[:40]: # only check the 40 best candidate LCMs
        per = item['period']
        res = item['residues']
        
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
    new_count = bin(uncovered).count('1')
    print(f'Step {step} (Expand): Added {best_p}, LCM = {current_lcm}, uncovered = {new_count}, ratio = {best_ratio:.5f}', flush=True)
    step += 1
