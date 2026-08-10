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

# 7 base primes and their residues mod p^2
base_primes = [3, 11, 31, 19, 23, 47, 59]
base_residues = {3: 1, 11: 13, 31: 469, 19: 82, 23: 329, 47: 21, 59: 69}

moduli = [2] + [p**2 for p in base_primes]
residues = [1] + [base_residues[p] for p in base_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}")
print(f"prod = {base_prod} (digits: {len(str(base_prod))})")

def is_blocked_very_fast(diff):
    for p in base_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    for p in small_primes:
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
            
        # Verify the double condition: diff % p == 0 and diff % p^2 != 0
        if diff % found_p == 0 and diff % (found_p*found_p) != 0:
            blocking_primes[v] = found_p
        else:
            # Let's find another prime congruent to 3 mod 4 that satisfies the simple modulo condition!
            # If none exists, we can use found_p but we would need to be careful.
            # Actually, if exp is odd, is it always true that we can find some prime with odd exponent?
            # Yes, but we need the simple modulo condition. Let's find any prime p with odd exponent and check if p^2 does not divide diff.
            # Wait, if exp is odd, and exp >= 3, then p^2 divides diff, so we cannot use p.
            # But if there is any other prime q with odd exponent = 1, we can use q!
            # Let's check:
            success_v = False
            for q, e in factors:
                if q % 4 == 3 and e % 2 != 0:
                    if diff % q == 0 and diff % (q*q) != 0:
                        blocking_primes[v] = int(q)
                        success_v = True
                        break
            if not success_v:
                return None
    return blocking_primes

def worker(worker_id, k_start, k_end, shutdown_event):
    print(f"Worker {worker_id} started: k in [{k_start}, {k_end}]", flush=True)
    
    for k in range(k_start, k_end):
        if shutdown_event.is_set():
            break
            
        N = N0 + k * base_prod
        if N <= 1:
            continue
        if N >= 1.27 * 10**24: # math limit for s < 40 and i < 160
            break
            
        if check_candidate_very_fast(N):
            bp = confirm_candidate(N)
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
    k_max = 5000000
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
