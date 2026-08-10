import sys
import time

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

# Use the CRT base from find_crt_counterexample.py
# Moduli and residues for N mod p^2
# p=3 r=1
# p=11 r=2
# p=19 r=41
# p=23 r=120
# p=31 r=225
moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base = int(crt(residues, moduli))
prod = int(1)
for m in moduli:
    prod *= m

print(f"Base CRT solved: N0 = {n_base}, prod = {prod} (digits: {len(str(prod))})")
sys.stdout.flush()

# Precompute a small prime pool up to 1000 for quick filtering
small_primes = [p for p in prime_range(3, 1000) if p % 4 == 3]

# We will search starting from k = 1
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
            
    # If too many elements are unblocked, we can continue (optional, but let's check all remaining using Sage factor)
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
        
    if k % 100 == 0:
        print(f"Checked up to k = {k} (time: {time.time() - start_time:.2f}s)...", flush=True)

print(f"Search finished in {time.time() - start_time:.2f}s.")
