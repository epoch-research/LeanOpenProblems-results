import sys
import time
from multiprocessing import Process, Event

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()
small_primes = [p for p in prime_range(3, 2000) if p % 4 == 3]

# Greedily select 7 primes from the pool of small primes
primes_pool = [3, 11, 31, 19, 23, 43, 47, 59, 67, 71, 79, 83]

N_max = 10**12
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]
print(f"V_target size for 10^12: {len(V_target)}")

selected_primes = []
selected_residues = {}
uncovered = list(V_target)

# We greedily pick 7 primes
for step in range(7):
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
    print(f"Prime {best_p}, Residue {best_r} (covers {best_cov}). Uncovered remaining: {len(uncovered)}")

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}")
print(f"prod = {base_prod} (digits: {len(str(base_prod))})")

def is_blocked_fast(diff):
    for p in selected_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    for p in small_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    # Fallback to Sage factor
    factors = factor(diff)
    for p, exp in factors:
        if p % 4 == 3 and exp % 2 != 0:
            return int(p)
    return None

def check_candidate(N):
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    blocking_primes = {}
    for v in V_actual:
        p = is_blocked_fast(N2 - v)
        if p is None:
            return None
        blocking_primes[v] = p
    return blocking_primes

def worker(worker_id, k_start, k_end, shutdown_event):
    print(f"Worker {worker_id} started: k in [{k_start}, {k_end}]", flush=True)
    last_print = time.time()
    
    for k in range(k_start, k_end):
        if shutdown_event.is_set():
            break
            
        N = N0 + k * base_prod
        if N <= 1:
            continue
        if N >= 10**15:
            break
            
        bp = check_candidate(N)
        if bp is not None:
            print(f"\nSUCCESS! Worker {worker_id} found counterexample N = {N} (k = {k})", flush=True)
            print(f"N^2 = {N*N}", flush=True)
            print(f"V_all size = {len([v for v in all_V if v < N*N])}", flush=True)
            print(f"blocking_primes = {bp}", flush=True)
            
            with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
                f.write(f"N = {N}\n")
                f.write(f"blocking_primes = {bp}\n")
            shutdown_event.set()
            break

if __name__ == "__main__":
    k_max = 100000
    num_workers = 32
    step = k_max // num_workers
    
    shutdown_event = Event()
    processes = []
    
    start_time_global = time.time()
    
    for i in range(num_workers):
        w_start = i * step
        w_end = (i+1) * step if i < num_workers - 1 else k_max
        p = Process(target=worker, args=(i, w_start, w_end, shutdown_event))
        processes.append(p)
        p.start()
        
    try:
        while not shutdown_event.is_set():
            alive = False
            for p in processes:
                if p.is_alive():
                    alive = True
                    break
            if not alive:
                print("All processes finished search.", flush=True)
                break
            time.sleep(1)
    except KeyboardInterrupt:
        print("Interrupted! Terminating processes...")
        shutdown_event.set()
        
    for p in processes:
        p.join(timeout=1)
        if p.is_alive():
            p.terminate()
            
    print(f"Done in {time.time() - start_time_global:.2f}s.", flush=True)
