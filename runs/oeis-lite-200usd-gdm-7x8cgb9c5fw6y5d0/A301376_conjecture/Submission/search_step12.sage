import sys
import time

def is_sum_of_two_squares_exact(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    factors = factor(n)
    for p, exp in factors:
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def get_V_all_correct(limit):
    V = {1}
    for s in range(50):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(100):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()
print(f"Precomputed {len(all_V_precomputed)} possible v values.")

# Generate the 13 base primes and residues
print("Step 1: Finding the 13 base primes and residues...", flush=True)
primes_pool = [p for p in prime_range(3, 1000) if p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 3}
prod = 21

for step in range(1, 13):
    limit = prod
    V_all_unblocked = get_V_all_correct(limit)
    unblocked = []
    for v in V_all_unblocked:
        blocked = False
        for p, r in res_dict.items():
            r2 = (r*r) % p
            if v % p == r2:
                blocked = True
                break
        if not blocked:
            unblocked.append(v)
            
    best_p = None
    best_r = None
    best_cov = -1
    for p in primes_pool:
        if p in res_dict:
            continue
        cov_for_r = [0] * p
        for v in unblocked:
            v_mod = v % p
            if v_mod == 0:
                cov_for_r[0] += 1
            elif pow(v_mod, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod:
                        cov_for_r[x] += 1
                        cov_for_r[p - x] += 1
                        break
        max_cov = max(cov_for_r)
        best_r_for_p = cov_for_r.index(max_cov)
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p

# Solve CRT to find the base
moduli = [p for p in primes]
residues = [res_dict[p] for p in primes]
n_base = int(crt(residues, moduli))
if n_base % 2 == 0:
    n_base += prod

print(f"Base solved: N0 = {n_base}, prod = {prod} (digits: {len(str(prod))})")
sys.stdout.flush()

# Precompute a medium prime pool up to 5,000 for fast initial filtering
small_primes = [p for p in prime_range(3, 5000) if p % 4 == 3]
print(f"Generated filtering pool of {len(small_primes)} primes up to 5,000.")

print("Step 2: Searching for true counterexample N...", flush=True)
start_time = time.time()
for k in range(1, 100000):
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    
    # Ensure N < 1.27 * 10^24
    if N >= 1.27 * 10**24:
        print("N exceeded the limit of 1.27 * 10^24!")
        break
        
    V_all = [v for v in all_V_precomputed if v < N2]
    
    # Quick filter with small primes
    unblocked = []
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        found_p = None
        for p in small_primes:
            if diff % p == 0 and diff % (p*p) != 0:
                found_p = p
                break
        if found_p is not None:
            blocking_primes[v] = found_p
        else:
            unblocked.append(v)
            
    # Check all remaining using Sage factor
    all_blocked = True
    for v in unblocked:
        diff = N2 - v
        factors = factor(diff)
        found_p = None
        for p, exp in factors:
            if p % 4 == 3 and exp % 2 != 0:
                found_p = int(p)
                break
        if found_p is not None:
            blocking_primes[v] = found_p
        else:
            all_blocked = False
            break
            
    if k % 10 == 0:
        print(f"k = {k}: checked {len(V_all)} elements ({len(unblocked)} required factor) in {time.time() - start_time:.2f}s", flush=True)
        
    if all_blocked:
        print(f"\nSUCCESS! FOUND TRUE COUNTEREXAMPLE N = {N} (k = {k})")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len(V_all)}")
        print(f"Number of distinct blocking primes used: {len(set(blocking_primes.values()))}")
        sys.stdout.flush()
        
        # Save results
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break

print(f"Search finished in {time.time() - start_time:.2f}s.")
