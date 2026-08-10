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

    # Generate S1 with a=0, S2 with c=0
    S1_vals = []
    b = 0
    while True:
        val = 3**b
        if val**2 > N:
            break
        S1_vals.append(val**2)
        b += 1
        
    S2_vals = []
    d = 0
    while True:
        val = 5**d
        if val**2 > N:
            break
        S2_vals.append(val**2)
        d += 1
            
    failed = []
    for n in range(2, N + 1):
        if n % 4 == 0:
            continue
        found = False
        for t1 in S1_vals:
            if t1 > n:
                break
            for t2 in S2_vals:
                rem = n - t1 - t2
                if rem < 0:
                    break
                if is_sum2sq[rem]:
                    found = True
                    break
            if found:
                break
        if not found:
            failed.append(n)
            if len(failed) > 10:
                break
    if not failed:
        print(f"Success for a=0, c=0 up to {N}!")
    else:
        print(f"Failed for a=0, c=0. Some failures: {failed}")

check(100000)
