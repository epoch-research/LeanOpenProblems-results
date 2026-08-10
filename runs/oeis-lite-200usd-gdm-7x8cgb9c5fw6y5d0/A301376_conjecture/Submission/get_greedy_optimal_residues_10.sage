def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()
primes_pool = [p for p in prime_range(3, 1000) if p % 4 == 3]

# We optimize residues for N up to 10^15
N_max = 10**15
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]

selected_primes = []
selected_residues = {}
uncovered = list(V_target)

for step in range(10):
    best_p = None
    best_r = None
    best_cov = -1
    
    for p in primes_pool:
        if p in selected_primes:
            continue
        cov_for_r = [0] * p
        for v in uncovered:
            v_mod = v % p
            if v_mod == 0:
                cov_for_r[0] += 1
            elif pow(v_mod, (p-1)//2, p) == 1:
                for r in range(1, p):
                    if (r*r) % p == v_mod:
                        cov_for_r[r] += 1
                        cov_for_r[p-r] += 1
                        break
        max_cov = max(cov_for_r)
        best_r_for_p = cov_for_r.index(max_cov)
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    if best_cov <= 0:
        break
        
    selected_primes.append(best_p)
    selected_residues[best_p] = best_r
    new_uncovered = []
    r2 = (best_r * best_r) % best_p
    for v in uncovered:
        if v % best_p != r2:
            new_uncovered.append(v)
    uncovered = new_uncovered

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"selected_primes = {selected_primes}")
print(f"selected_residues = {[selected_residues[p] for p in selected_primes]}")
print(f"N0 = {N0}")
print(f"prod = {base_prod}")
print(f"uncovered remaining = {len(uncovered)}")
