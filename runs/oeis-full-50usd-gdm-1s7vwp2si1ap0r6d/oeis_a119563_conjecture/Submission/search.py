import sympy
from math import lcm, gcd

def multiplicative_order(a, n):
    if n == 1: return 1
    if gcd(a, n) != 1: return 0
    curr = a % n
    d = 1
    while curr != 1:
        curr = (curr * a) % n
        d += 1
    return d

print('Collecting primes up to 500...')
analyzed = []
for p in sympy.primerange(3, 500):
    d = multiplicative_order(2, p)
    if d == 0: continue
    
    b = d
    a_pow = 0
    while b % 2 == 0:
        b //= 2
        a_pow += 1
    
    if b == 1:
        period = 1
    else:
        period = multiplicative_order(2, b)
        if period == 0: continue
            
    overall_period = lcm(d, period)
    if overall_period > 100000:
        continue
    
    matching_residues = []
    for r in range(a_pow, a_pow + overall_period):
        term1 = pow(2, pow(2, r, d), p)
        term2 = pow(2, r, p)
        if (term1 + term2 - 1) % p == 0:
            matching_residues.append(r % overall_period)
            
    if matching_residues:
        analyzed.append({
            'prime': p,
            'period': overall_period,
            'residues': matching_residues
        })

print(f'Collected {len(analyzed)} primes.')

# Initial state: residues {0, 1, 2, 3, 4} mod 6 are uncovered (since 5 is covered by 7)
current_lcm = 6
uncovered = 31 # binary 11111 (bits 0,1,2,3,4 are 1, bit 5 is 0)
used_primes = [7]

step = 0
while step < 50:
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
        if new_lcm > 5000000: # limit LCM size
            continue
            
        # Expand current uncovered
        expanded = uncovered * (((1 << new_lcm) - 1) // ((1 << current_lcm) - 1))
        expanded &= ~31
        
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
        print('No prime could be added within LCM limit.')
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
