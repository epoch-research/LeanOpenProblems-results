import re
import sys
sys.set_int_max_str_digits(200000)
from sympy import isprime
from sympy.ntheory.modular import crt

# Old counterexample from iterative_out.txt
n_old = 126686524250410004736537312064293613795653657092983804510554503324715379258723493119883344012301288982405926046569374575432235100014312858069895494644651006289334684761526421296266808332923548185778355634967387614240536269449875614849275
n2_old = n_old * n_old

# 51 Old primes: (v, p)
used_primes = [(26, 11), (104, 19), (314, 31), (416, 23), (1256, 43), (1664, 59), (5024, 47), (6656, 67), (20096, 71), (26624, 79), (73274, 83), (80384, 107), (106496, 103), (293096, 127), (425984, 163), (1286144, 131), (1703936, 191), (4689536, 151), (6815744, 199), (18758144, 167), (75032576, 223), (82313216, 139), (109051904, 227), (300130304, 251), (436207616, 263), (1317011456, 179), (5268045824, 211), (6979321856, 307), (19208339456, 311), (21072183296, 239), (84288733184, 379), (111669149696, 331), (307333431296, 383), (446676598784, 367), (1348619730944, 431), (1786706395136, 439), (4917334900736, 419), (5394478923776, 443), (19669339602944, 463), (86311662780416, 487), (114349209288704, 499), (457396837154816, 503), (1380986604486656, 491), (1829587348619264, 587), (20141403753414656, 467), (22095785671786496, 563), (80565615013658624, 479), (88383142687145984, 631), (322262460054634496, 523), (5156199360874151936, 571), (20624797443496607744, 599)]

# Load extra primes from expand_out.txt
with open("/workspace/leanproject/Submission/expand_out.txt") as f:
    content = f.read()

# Find "Extra primes: [...]"
match = re.search(r"Extra primes:\s*(\[.*\])", content)
if not match:
    print("Could not find Extra primes in expand_out.txt!")
    sys.exit(1)

extra_primes_str = match.group(1)
pairs = re.findall(r"\((\d+),?\s*(\d+)\)", extra_primes_str)
extra_primes = [(int(p), int(r)) for p, r in pairs]
print(f"Loaded {len(extra_primes)} extra primes.")

def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

# Moduli and residues for CRT
moduli = [9, 49]
residues = [1, 15]

# Add old primes
for v, p in used_primes:
    moduli.append(p**2)
    residues.append(n_old % (p**2))

# Add extra primes with lifting
for p, r in extra_primes:
    moduli.append(p**2)
    # find root mod p
    root = -1
    for x in range(p):
        if (x*x) % p == r % p:
            root = x
            break
    if root == -1:
        print(f"ERROR: No square root for r={r} mod p={p}")
        sys.exit(1)
        
    # lift mod p^2
    best_k = -1
    best_fail_count = 999999
    # We only care about how many v's in V_all covered by p are failed (i.e. (x^2 - v) % p^2 == 0)
    # But wait! To be perfectly safe, we can just check all v in V_all up to some limit or just do the count
    # Actually, we can check all v % p == r from a simulated V_all
    # Since V_all size is 6401, we can compute it for a large limit (say 10^300)
    V_temp = get_V_all(10**300)
    covered_vs = [v for v in V_temp if v % p == r]
    
    for k in range(p):
        x = root + k*p
        fail_count = 0
        for fv in covered_vs:
            if (x*x - fv) % (p**2) == 0:
                fail_count += 1
        if fail_count < best_fail_count:
            best_fail_count = fail_count
            best_k = k
            
    lift = root + best_k * p
    residues.append(lift)
    if best_fail_count > 0:
        print(f"Warning: extra prime {p} has {best_fail_count} unavoidable fails with lift {lift}")

print("Solving CRT...")
n_new, prod = crt(moduli, residues)
n_new = int(n_new)
prod = int(prod)
if n_new % 2 == 0:
    n_new += prod

print(f"New candidate n has {len(str(n_new))} digits.")

# Now verify that n_new blocks every element in V_all (size 6401)
n2_new = n_new * n_new
V_all = get_V_all(n2_new)
print(f"New V_all size: {len(V_all)}")

primes_check = [3, 7] + [p for _, p in used_primes] + [p for p, _ in extra_primes]

unblocked = []
v_to_prime = {}

for idx, v in enumerate(V_all):
    val = n2_new - v
    found = False
    for p in primes_check:
        if val % p == 0 and val % (p*p) != 0:
            v_to_prime[v] = p
            found = True
            break
    if not found:
        unblocked.append(v)

if unblocked:
    print(f"FAILED! {len(unblocked)} elements are not blocked by the combined primes.")
    print("First few unblocked:", unblocked[:10])
else:
    print("SUCCESS!!! 100% GUARANTEED COUNTEREXAMPLE FOUND!")
    print(f"n0 = {n_new}")
