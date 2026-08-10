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

all_V = precompute_V()

print("Searching for true counterexample N...", flush=True)
start_time = time.time()
found = False

for N in range(100001, 5000000, 2):
    if N % 50000 == 1:
        print(f"N = {N}... elapsed: {time.time() - start_time:.2f}s", flush=True)
        
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    all_blocked = True
    blocking_primes = {}
    for v in V_actual:
        diff = N2 - v
        # Check if diff is a sum of two squares
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
        print(f"\nSUCCESS! Found counterexample N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len(V_actual)}")
        print(f"blocking_primes = {blocking_primes}")
        found = True
        
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break

if not found:
    print("No counterexample found up to 5,000,000.")
