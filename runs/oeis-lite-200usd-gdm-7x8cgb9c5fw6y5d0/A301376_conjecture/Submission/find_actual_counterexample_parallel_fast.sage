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

# 5 base primes
selected_primes = [3, 11, 31, 19, 23]

# Residues optimized for N up to 10^10
selected_residues = {3: 1, 11: 2, 31: 4, 19: 5, 23: 2}

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}")
print(f"prod = {base_prod}")

def is_blocked_very_fast(diff):
    # Only trial division, extremely fast!
    for p in small_primes:
        # Check if p divides diff with odd exponent
        if diff % p == 0:
            count = 0
            while diff % p == 0:
                count += 1
                diff //= p
            if count % 2 != 0:
                return p
    return None

def check_candidate_very_fast(N):
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    for v in V_actual:
        p = is_blocked_very_fast(N2 - v)
        if p is None:
            return False
    return True

def confirm_candidate(N):
    # Double check using exact factorization
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    blocking_primes = {}
    for v in V_actual:
        diff = N2 - v
        factors = factor(diff)
        found_p = None
        for p, exp in factors:
            if p % 4 == 3 and exp % 2 != 0:
                found_p = int(p)
                break
        if found_p is None:
            return None
        blocking_primes[v] = found_p
    return blocking_primes

def worker(worker_id, k_start, k_end, shutdown_event):
    print(f"Worker {worker_id} started: k in [{k_start}, {k_end}]", flush=True)
    
    for k in range(k_start, k_end):
        if shutdown_event.is_set():
            break
            
        N = N0 + k * base_prod
        if N <= 1:
            continue
        if N >= 10**13: # safe limit
            break
            
        if check_candidate_very_fast(N):
            # Double check with complete factorization
            bp = confirm_candidate(N)
            if bp is not None:
                print(f"\nSUCCESS! Worker {worker_id} found counterexample N = {N} (k = {k})", flush=True)
                print(f"N^2 = {N*N}", flush=True)
                print(f"V_all size = {len([v for v in all_V if v < N*N])}", flush=True)
                print(f"blocking_primes = {bp}", flush=True)
                
                # Save results
                with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
                    f.write(f"N = {N}\n")
                    f.write(f"blocking_primes = {bp}\n")
                shutdown_event.set()
                break

if __name__ == "__main__":
    k_max = 200000
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
