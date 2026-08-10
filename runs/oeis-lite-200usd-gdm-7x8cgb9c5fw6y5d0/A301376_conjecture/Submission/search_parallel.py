import sys
import time
from sympy import isprime
from multiprocessing import Pool, cpu_count

def get_V_all(N2):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2:
                V.add(val)
    return sorted(list(V))

# Precompute primes mod 3 mod 4 up to 100,000 (Lean can handle these instantly)
primes_3mod4_limit = [p for p in range(3, 100000) if p % 4 == 3 and isprime(p)]
V_max = get_V_all(1.5 * 10**14) # Precompute V up to N = 12*10^6

def check_range(args):
    start_N, end_N = args
    for N in range(start_N, end_N):
        N2 = N * N
        V_all = [v for v in V_max if v < N2]
        
        all_blocked = True
        blocking_primes = {}
        for v in V_all:
            diff = N2 - v
            if diff == 0:
                all_blocked = False
                break
            found = False
            for p in primes_3mod4_limit:
                if p * p > diff:
                    break
                if diff % p == 0 and diff % (p*p) != 0:
                    blocking_primes[v] = p
                    found = True
                    break
            if not found:
                all_blocked = False
                break
                
        if all_blocked:
            return N, blocking_primes
    return None

if __name__ == "__main__":
    cores = cpu_count()
    print(f"Starting parallel search on {cores} cores...")
    sys.stdout.flush()
    
    start_range = 1000000
    end_range = 12000000
    chunk_size = 50000
    
    ranges = []
    curr = start_range
    while curr < end_range:
        ranges.append((curr, min(curr + chunk_size, end_range)))
        curr += chunk_size
        
    t0 = time.time()
    with Pool(cores) as pool:
        for result in pool.imap_unordered(check_range, ranges):
            if result is not None:
                N, blocking_primes = result
                print(f"\nFOUND EASY COUNTEREXAMPLE N = {N}")
                print(f"N^2 = {N*N}")
                print(f"blocking_primes = {blocking_primes}")
                print(f"Time taken: {time.time() - t0:.2f}s")
                pool.terminate()
                sys.exit(0)
                
    print(f"Finished search up to {end_range} with no easy counterexample found.")
