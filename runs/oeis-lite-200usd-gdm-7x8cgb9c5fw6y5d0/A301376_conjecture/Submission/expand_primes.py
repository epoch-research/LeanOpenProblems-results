import sys
from sympy import isprime
from sympy.ntheory.modular import crt

n = 126686524250410004736537312064293613795653657092983804510554503324715379258723493119883344012301288982405926046569374575432235100014312858069895494644651006289334684761526421296266808332923548185778355634967387614240536269449875614849275
n2 = n*n

# Existing 53 primes
used_primes = [(26, 11), (104, 19), (314, 31), (416, 23), (1256, 43), (1664, 59), (5024, 47), (6656, 67), (20096, 71), (26624, 79), (73274, 83), (80384, 107), (106496, 103), (293096, 127), (425984, 163), (1286144, 131), (1703936, 191), (4689536, 151), (6815744, 199), (18758144, 167), (75032576, 223), (82313216, 139), (109051904, 227), (300130304, 251), (436207616, 263), (1317011456, 179), (5268045824, 211), (6979321856, 307), (19208339456, 311), (21072183296, 239), (84288733184, 379), (111669149696, 331), (307333431296, 383), (446676598784, 367), (1348619730944, 431), (1786706395136, 439), (4917334900736, 419), (5394478923776, 443), (19669339602944, 463), (86311662780416, 487), (114349209288704, 499), (457396837154816, 503), (1380986604486656, 491), (1829587348619264, 587), (20141403753414656, 467), (22095785671786496, 563), (80565615013658624, 479), (88383142687145984, 631), (322262460054634496, 523), (5156199360874151936, 571), (20624797443496607744, 599)]

primes_set = {3, 7}
for v, p in used_primes:
    primes_set.add(p)

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

print("Generating full V_all...")
V_all = get_V_all(n2)
print(f"Full V_all size: {len(V_all)}")

failing = []
for idx, v in enumerate(V_all):
    val = n2 - v
    found_block = False
    for p in [3, 7] + [p for _, p in used_primes]:
        if val % p == 0 and val % (p*p) != 0:
            found_block = True
            break
    if not found_block:
        failing.append(v)

print(f"Number of failing v's to block: {len(failing)}")

print("Precomputing new candidate primes congruent to 3 mod 4...")
candidate_primes = [p for p in range(11, 20000) if isprime(p) and p % 4 == 3 and p not in primes_set]
print(f"Found {len(candidate_primes)} candidates.")

# We want to greedily choose extra primes to cover the failing v's
# But wait! For each chosen prime, we must also specify a residue r (which is a quadratic residue)
# and we will lift it to p^2.
# Wait! Since we are keeping the existing moduli and residues, we already have n mod 9, 49, p^2.
# If we add a new prime p, we can choose any root r mod p (which is a QR), and then lift it to p^2.
# Then the new CRT will give a new candidate n_new.
# For n_new, we will have:
# n_new = n mod P (the old product of squares)
# n_new = lift mod p^2.
# So n_new^2 = n^2 = v mod p for all the old covered v's!
# And for the new prime p, n_new^2 = lift^2 = r = v mod p for the v's covered by p!
# So yes, n_new will block all the old covered v's, AND the new covered v's!
# This is mathematically 100% correct!

uncovered = set(failing)
extra_primes = [] # list of (p, r)

while uncovered:
    best_p = None
    best_r = None
    best_covered = set()
    
    for p in candidate_primes:
        if p in [ep[0] for ep in extra_primes]:
            continue
        # count frequencies of v % p for v in uncovered
        freq = {}
        for v in uncovered:
            r = v % p
            freq[r] = freq.get(r, 0) + 1
            
        for r, count in freq.items():
            if count > len(best_covered):
                # check if r is QR
                if r == 0 or pow(r, (p-1)//2, p) == 1:
                    covered = set(v for v in uncovered if v % p == r)
                    best_covered = covered
                    best_p = p
                    best_r = r
                    
    if len(best_covered) == 0:
        print("ERROR: Could not find any prime to block remaining!")
        print(uncovered)
        sys.exit(1)
        
    extra_primes.append((best_p, best_r))
    uncovered -= best_covered
    print(f"Selected prime {best_p} with residue {best_r} (blocked {len(best_covered)} elements). Remaining: {len(uncovered)}")

print(f"\nSuccessfully blocked all! Total extra primes: {len(extra_primes)}")
print(f"Extra primes: {extra_primes}")
