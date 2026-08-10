import math
import numpy as np

def main():
    limit = 2000005
    print("Computing totients...", flush=True)
    phi = np.arange(limit, dtype=np.int64)
    for i in range(2, limit):
        if phi[i] == i:
            for j in range(i, limit, i):
                phi[j] -= phi[j] // i
    print("Done.", flush=True)

    # Find the largest prime factor of each number
    print("Computing largest prime factors...", flush=True)
    lpf = np.arange(limit, dtype=np.int32)
    for i in range(2, limit):
        if lpf[i] == i:
            for j in range(i, limit, i):
                lpf[j] = i
    print("Done.", flush=True)

    def is_square(x):
        r = int(math.isqrt(x))
        return r * r == x

    # We will search for different thresholds: 300, 500, 1000
    for threshold in [300, 500, 1000]:
        uncovered_without_good_k = []
        for n in range(9, 2000001):
            if n % 3 == 0 or n % 10 == 0:
                continue
            
            limit_k = (n - 1) // 2
            found = False
            for k in range(1, limit_k + 1):
                prod = int(phi[k]) * int(phi[n - k])
                if is_square(prod):
                    if lpf[n - k] <= threshold and lpf[k] <= threshold:
                        found = True
                        break
            if not found:
                uncovered_without_good_k.append(n)
                break
                
        print(f"For threshold {threshold}: first failure at n = {uncovered_without_good_k[0] if len(uncovered_without_good_k) > 0 else 'NONE (100% COVERED!)'}")

if __name__ == "__main__":
    main()
