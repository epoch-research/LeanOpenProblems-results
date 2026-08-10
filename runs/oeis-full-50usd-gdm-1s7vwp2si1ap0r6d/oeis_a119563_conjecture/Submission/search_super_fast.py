from sage.all import *

print('Starting super-fast prime search...')
analyzed = []
for p in primes(3, 1000000):
    try:
        d = GF(p)(2).multiplicative_order()
    except:
        continue
    
    # Skip if d is a power of 2
    if (d & (d - 1)) == 0:
        continue
        
    b = d
    a_pow = 0
    while b % 2 == 0:
        b //= 2
        a_pow += 1
        
    try:
        period = GF(b)(2).multiplicative_order()
    except:
        continue
        
    overall_period = lcm(d, period)
    if overall_period > 100000: # limit period to 100,000
        continue
        
    # Check matching residues
    matching_residues = []
    start = max(5, a_pow)
    for r in range(start, start + overall_period):
        pow2_r_mod_d = power_mod(2, r, d)
        t1 = power_mod(2, pow2_r_mod_d, p)
        t2 = power_mod(2, r, p)
        if (t1 + t2 - 1) % p == 0:
            matching_residues.append(r % overall_period)
            
    if matching_residues:
        analyzed.append({
            'prime': int(p),
            'period': int(overall_period),
            'residues': [int(r) for r in matching_residues]
        })

print(f'Collected {len(analyzed)} primes.')
# Write to a file for later use
import json
with open('analyzed_primes.json', 'w') as f:
    json.dump(analyzed, f)
