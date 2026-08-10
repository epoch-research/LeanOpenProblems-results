from sympy import isprime
from sympy.ntheory.modular import crt

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()

moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

prime_pool = [p for p in range(3, 5000) if isprime(p) and p % 4 == 3]

for k in range(1, 11):
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    V_all = [v for v in all_V_precomputed if v < N2]
    
    unblocked = []
    for v in V_all:
        diff = N2 - v
        found_block = False
        for p in prime_pool:
            if diff % p == 0 and diff % (p*p) != 0:
                found_block = True
                break
        if not found_block:
            unblocked.append(v)
    print(f"k = {k}, V_all size = {len(V_all)}, unblocked count = {len(unblocked)}")
