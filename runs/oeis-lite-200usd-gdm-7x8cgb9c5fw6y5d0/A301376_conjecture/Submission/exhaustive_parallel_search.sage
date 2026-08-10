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

def is_blocked_fast(diff):
    for p in small_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    # Fallback to factor
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

def worker(worker_id, start_N, end_N, shutdown_event):
    if start_N % 2 == 0:
        start_N += 1
        
    print(f"Worker {worker_id} started: [{start_N}, {end_N}]", flush=True)
    last_print = time.time()
    
    for N in range(start_N, end_N, 2):
        if shutdown_event.is_set():
            break
            
        if worker_id == 0 and time.time() - last_print > 10:
            print(f"Worker 0 at N = {N}... time elapsed: {time.time() - start_time_global:.2f}s", flush=True)
            last_print = time.time()
            
        bp = check_candidate(N)
        if bp is not None:
            print(f"\nSUCCESS! Worker {worker_id} found counterexample N = {N}", flush=True)
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
    N_start = 100001
    N_end = 20000000
    num_workers = 32
    
    step = (N_end - N_start) // num_workers
    shutdown_event = Event()
    processes = []
    
    start_time_global = time.time()
    
    for i in range(num_workers):
        w_start = N_start + i * step
        w_end = N_start + (i+1) * step if i < num_workers - 1 else N_end
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
