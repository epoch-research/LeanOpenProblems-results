def solve():
    limit = 1000000
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    pos = [0]*limit
    neg = [0]*limit
    p_count = 0
    n_count = 0
    for i in range(limit):
        if a[i] > 0:
            p_count += 1
        elif a[i] < 0:
            n_count += 1
        pos[i] = p_count
        neg[i] = n_count
        
    # We want to check if (pos[b+6] - neg[b+6]) - (pos[b] - neg[b]) <= 2
    # pos - neg is D
    # so D(b+6) - D(b) <= 2
    max_increase = -10
    min_increase = 10
    for b in range(limit - 6):
        D_b = pos[b] - neg[b]
        D_b6 = pos[b+6] - neg[b+6]
        inc = D_b6 - D_b
        if inc > max_increase:
            max_increase = inc
            max_at = b
        if inc < min_increase:
            min_increase = inc
            min_at = b
            
    print(f"Max increase in 6 steps: {max_increase} at b={max_at}")
    print(f"Min increase in 6 steps: {min_increase} at b={min_at}")

solve()
