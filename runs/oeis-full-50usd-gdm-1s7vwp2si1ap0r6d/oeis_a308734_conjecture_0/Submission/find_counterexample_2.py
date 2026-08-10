import math

def find_counterexamples(N):
    # Precompute sums of two squares up to N
    is_sum2sq = [False] * (N + 1)
    limit = int(math.isqrt(N))
    for x in range(limit + 1):
        x2 = x * x
        for y in range(x, limit + 1):
            s = x2 + y * y
            if s > N:
                break
            is_sum2sq[s] = True
            
    # Generate S1^2 and S2^2 lists
    S1_sq = []
    a = 0
    while True:
        p2 = 2**a
        if p2**2 > N:
            break
        b = 0
        while True:
            val = p2 * (3**b)
            if val**2 > N:
                break
            S1_sq.append(val**2)
            b += 1
        a += 1
    
    S2_sq = []
    c = 0
    while True:
        p2 = 2**c
        if p2**2 > N:
            break
        d = 0
        while True:
            val = p2 * (5**d)
            if val**2 > N:
                break
            S2_sq.append(val**2)
            d += 1
        c += 1

    # Sort S1_sq and S2_sq to process smaller ones first
    S1_sq.sort()
    S2_sq.sort()

    print(f"S1_sq count: {len(S1_sq)}, S2_sq count: {len(S2_sq)}")

    # Let's do the check for each n
    for n in range(2, N + 1):
        found = False
        for t1 in S1_sq:
            if t1 > n:
                break
            for t2 in S2_sq:
                rem = n - t1 - t2
                if rem < 0:
                    break
                if is_sum2sq[rem]:
                    found = True
                    break
            if found:
                break
        if not found:
            print(f"Counterexample found: n = {n}")
            return
    print(f"No counterexample found up to {N}")

find_counterexamples(2000000)
