import numpy as np
import math
import sys

def main():
    limit = 2000005
    print("Computing totients...", flush=True)
    phi = np.arange(limit, dtype=np.int64)
    for i in range(2, limit):
        if phi[i] == i:
            for j in range(i, limit, i):
                phi[j] -= phi[j] // i
    print("Done computing totients.", flush=True)

    # Pre-identify squares
    print("Pre-identifying squares...", flush=True)
    max_phi_prod = limit * limit # rough upper bound
    # We will just use math.isqrt or integer square check since we want to be absolutely correct.
    # Actually, math.isqrt is extremely fast in Python.

    print("Searching witnesses...", flush=True)
    max_k = 0
    k_counts = [0] * 10000
    
    # We will keep track of witnesses
    witnesses = []
    
    # We can run a fast loop
    for n in range(9, 2000001):
        if n % 3 == 0 or n % 10 == 0:
            continue
        
        # Search for witness k
        limit_k = (n - 1) // 2
        found = False
        for k in range(1, limit_k + 1):
            prod = int(phi[k]) * int(phi[n - k])
            r = int(math.isqrt(prod))
            if r * r == prod:
                witnesses.append(k)
                if k > max_k:
                    max_k = k
                if k < 10000:
                    k_counts[k] += 1
                found = True
                break
        if not found:
            print(f"CRITICAL: No witness found for n = {n}!")
            sys.exit(1)
            
        if n % 200000 == 0:
            print(f"Processed up to {n}...", flush=True)
            
    print(f"All witnesses found successfully!")
    print(f"Maximum witness k: {max_k}")
    
    # Let's count how many witnesses are > 255
    gt_255 = sum(1 for w in witnesses if w > 255)
    print(f"Witnesses > 255: {gt_255}")
    # Let's count how many are > 65535
    gt_65535 = sum(1 for w in witnesses if w > 65535)
    print(f"Witnesses > 65535: {gt_65535}")

if __name__ == "__main__":
    main()
