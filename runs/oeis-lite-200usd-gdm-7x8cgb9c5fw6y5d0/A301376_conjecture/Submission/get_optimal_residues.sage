def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()

# 13 base primes
selected_primes = [3, 11, 31, 43, 127, 23, 19, 59, 71, 83, 47, 67, 103]

N_max = 10**22
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]

selected_residues = {}
uncovered = list(V_target)

for p in selected_primes:
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
    best_r = cov_for_r.index(max_cov)
    selected_residues[p] = best_r
    
    # Remove covered
    new_uncovered = []
    r2 = (best_r * best_r) % p
    for v in uncovered:
        if v % p != r2:
            new_uncovered.append(v)
    uncovered = new_uncovered

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"N0 = {N0}")
print(f"prod = {base_prod}")
print(f"uncovered remaining = {len(uncovered)}")
