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

print('Collecting primes up to 5000...')
analyzed = []
for p in sympy.primerange(3, 5000):
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
    if overall_period > 1000000:
        continue
    
    matching_residues = []
    # We only care about n >= 5
    for r in range(max(5, a_pow), max(5, a_pow) + overall_period):
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

# We want to cover {5, 6, 7, 8, ...}
# Let's use a greedy search to cover all residues up to some large LCM
# Actually, let's represent the uncovered residues as a set of integers.
# To keep memory low, we can just track the uncovered residues of the current LCM.

current_lcm = 6
uncovered = {5} # mod 6, only 5 is >= 5 and needs covering (0,1,2,3,4 are prime)
used_primes = [7] # 7 covers 5 mod 6

# Let's do a backtracking or greedy search
for step in range(30):
    best_p = None
    best_uncovered = None
    best_lcm = None
    min_uncovered_count = 999999999
    
    for item in analyzed:
        p = item['prime']
        if p in used_primes:
            continue
        per = item['period']
        res = set(item['residues'])
        
        new_lcm = lcm(current_lcm, per)
        if new_lcm > 10000000: # Limit LCM to 10M
            continue
            
        # Lift current uncovered to new_lcm
        new_uncovered = set()
        for u in uncovered:
            for k in range(new_lcm // current_lcm):
                val = u + k * current_lcm
                # Check if val % per is in res (covered by p)
                if (val % per) not in res:
                    new_uncovered.add(val)
                    
        uncovered_count = len(new_uncovered)
        if uncovered_count < min_uncovered_count:
            min_uncovered_count = uncovered_count
            best_p = p
            best_uncovered = new_uncovered
            best_lcm = new_lcm
            
    if best_p is None:
        print('No prime could be added.')
        break
        
    current_lcm = best_lcm
    uncovered = best_uncovered
    used_primes.append(best_p)
    print(f'Step {step}: Added {best_p}, LCM = {current_lcm}, uncovered count = {len(uncovered)}', flush=True)
    if len(uncovered) == 0:
        print('FOUND COVERING SYSTEM!!!')
        print('Primes used:', used_primes)
        break
