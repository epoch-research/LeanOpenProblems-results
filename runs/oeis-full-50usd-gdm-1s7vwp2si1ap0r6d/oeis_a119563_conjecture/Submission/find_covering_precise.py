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
primes_list = list(primes(3, 1000))
prime_info = []
for p in primes_list:
    M, R = get_period_and_residues(p)
    if R and M <= 500:
        prime_info.append((p, M, R))

print(f"Collected {len(prime_info)} primes.")

# We want to cover {5, 6, 7, ...}.
# We can represent uncovered classes as a list of tuples (r, m) meaning r mod m.
# Initially, we only need to cover {5, 6, 7, ...}.
# Since we only care about n >= 5, let's start with the class (0, 1) mod 1,
# but we remember that 0, 1, 2, 3, 4 are already covered.
# So we can just split (0, 1) mod 1 into subclasses, and remove 0, 1, 2, 3, 4.
# Or simpler: we can just start with the uncovered classes mod 6:
# (0, 6), (1, 6), (2, 6), (3, 6), (4, 6)  (since (5, 6) is covered by 7).
uncovered_classes = [(0, 6), (1, 6), (2, 6), (3, 6), (4, 6)]

# Chinese Remainder Theorem helper
# Returns the single residue class mod lcm(m1, m2) that is the intersection of r1 mod m1 and r2 mod m2.
# If no intersection, returns None.
def intersect(r1, m1, r2, m2):
    g, x, y = xgcd(m1, m2)
    if (r1 - r2) % g != 0:
        return None
    # r = r1 - x * m1 * ((r1 - r2) // g)
    # modulo lcm(m1, m2)
    l = (m1 * m2) // g
    r = (r1 - x * m1 * ((r1 - r2) // g)) % l
    return r, l

# Subtract a covered class (uc, mc) from an uncovered class (r, m)
# Returns a list of disjoint subclasses mod lcm(m, mc) that partition (r, m) \ (uc, mc).
def subtract(r, m, uc, mc):
    inter = intersect(r, m, uc, mc)
    if inter is None:
        return [(r, m)]
    ri, li = inter
    # The intersection is ri mod li.
    # We want to partition r mod m into li/m subclasses mod li, and remove ri mod li.
    # The subclasses of r mod m mod li are: r + k*m mod li for k in 0..li/m-1.
    res = []
    for k in range(li // m):
        cand = (r + k * m) % li
        if cand != ri:
            res.append((cand, li))
    return res

# Let's do a greedy search
used_primes = [7]

for step in range(40):
    print(f"Step {step}: {len(uncovered_classes)} uncovered classes", flush=True)
    if len(uncovered_classes) == 0:
        print("SUCCESS! Covered everything!")
        print("Primes:", used_primes)
        break
        
    # Find the prime that removes the most/largest classes.
    # To measure "size" of uncovered, we can compute the sum of 1/m of the classes.
    # This is the density of the uncovered set.
    current_density = sum(1/m for r, m in uncovered_classes)
    print(f"  Current density: {float(current_density):.6f}", flush=True)
    if current_density < 1e-9:
        print("Density is practically zero! (Could be only extremely large n left, or we are done)")
        break
        
    best_p = None
    best_new_classes = None
    max_density_reduction = -1
    
    for p, M, R in prime_info:
        if p in used_primes:
            continue
            
        # Try to subtract all covered classes of p: (u, M) for u in R
        temp_classes = list(uncovered_classes)
        for u in R:
            next_classes = []
            for r, m in temp_classes:
                next_classes.extend(subtract(r, m, u, M))
            temp_classes = next_classes
            
        new_density = sum(1/m for r, m in temp_classes)
        reduction = current_density - new_density
        if reduction > max_density_reduction:
            max_density_reduction = reduction
            best_p = p
            best_new_classes = temp_classes
            
    if best_p is None or max_density_reduction <= 0:
        print("No prime can reduce density further.")
        break
        
    print(f"  Adding prime {best_p}, reduces density by {float(max_density_reduction):.6f}", flush=True)
    uncovered_classes = best_new_classes
    used_primes.append(best_p)
