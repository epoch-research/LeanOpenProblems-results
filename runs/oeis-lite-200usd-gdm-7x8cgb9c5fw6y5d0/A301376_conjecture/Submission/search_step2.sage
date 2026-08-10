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

# Generate the 2 base primes and residues (Step 2)
primes = [3, 7]
res_dict = {3: 1, 7: 3}
prod = 21

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
for k in range(1, 10000000):
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
            
    if k % 10000 == 0:
        print(f"k = {k}, N = {N}: checked {len(V_all)} elements ({len(unblocked)} required factor) in {time.time() - start_time:.2f}s", flush=True)
        
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
