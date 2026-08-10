import math

def check(N):
    is_sum2sq = [False] * (N + 1)
    limit = int(math.isqrt(N))
    for x in range(limit + 1):
        x2 = x * x
        for y in range(x, limit + 1):
            s = x2 + y * y
            if s > N:
                break
            is_sum2sq[s] = True

    for max_exp in [1, 2, 3]:
        print(f"Checking max_exp = {max_exp}")
        S1_vals = []
        for a in range(max_exp + 1):
            for b in range(max_exp + 1):
                val = (2**a) * (3**b)
                S1_vals.append(val**2)
        S2_vals = []
        for c in range(max_exp + 1):
            for d in range(max_exp + 1):
                val = (2**c) * (5**d)
                S2_vals.append(val**2)
                    
        failed = []
        for n in range(2, N + 1):
            if n % 4 == 0:
                continue
            found = False
            for t1 in S1_vals:
                if t1 > n:
                    continue
                for t2 in S2_vals:
                    rem = n - t1 - t2
                    if rem >= 0 and is_sum2sq[rem]:
                        found = True
                        break
                if found:
                    break
            if not found:
                failed.append(n)
                if len(failed) > 10:
                    break
        if not failed:
            print(f"Success for max_exp = {max_exp} up to {N}!")
        else:
            print(f"Failed for max_exp = {max_exp}. Some failures: {failed}")

check(10000000)
