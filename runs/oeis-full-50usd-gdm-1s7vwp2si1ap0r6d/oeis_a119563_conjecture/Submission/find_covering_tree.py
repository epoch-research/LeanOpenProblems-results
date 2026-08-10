from sage.all import *

def get_period_and_residues(p):
    try:
        d = GF(p)(2).multiplicative_order()
    except (ArithmeticError, ValueError):
        return None, []
    
    # We want to find the period of 2^n mod d.
    # Since d can be even, we write d = 2^a * b, where b is odd.
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
    # We check residues mod overall_period for n >= 5.
    # Since we need the behavior for n >= 5, and the pre-period is at most a_pow,
    # and max(5, a_pow) is the starting point, we can just check all residues r mod overall_period.
    # Since n >= 5, as long as overall_period >= 5 or we handle pre-period, it is fine.
    # To be safe, let's check residues r in range(max(5, a_pow), max(5, a_pow) + overall_period)
    # and reduce them mod overall_period.
    start = max(5, a_pow)
    for r in range(start, start + overall_period):
        pow2_r_mod_d = power_mod(2, r, d)
        t1 = power_mod(2, pow2_r_mod_d, p)
        t2 = power_mod(2, r, p)
        if (t1 + t2 - 1) % p == 0:
            matching_residues.append(r % overall_period)
            
    return overall_period, matching_residues

# Let's collect information for primes up to 2000
data = []
for p in primes(3, 2000):
    M, R = get_period_and_residues(p)
    if R:
        data.append({'p': p, 'M': M, 'R': R})

print(f"Collected {len(data)} useful primes.")
# Print some primes with small periods
data.sort(key=lambda x: x['M'])
for item in data[:20]:
    print(f"p={item['p']}, M={item['M']}, R={item['R']}")
