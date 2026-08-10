def solve():
    limit = 1000000000 # 1 billion
    
    pos = 0
    neg = 0
    max_diff = -1
    min_diff = 1000000000
    
    a_prev2 = 0
    a_prev1 = 1
    
    # b=0: a_prev2 = 0 (0)
    # b=1: a_prev1 = 1 (1)
    
    if a_prev2 > 0:
        pos += 1
    elif a_prev2 < 0:
        neg += 1
        
    diff = pos - neg
    if diff > max_diff:
        max_diff = diff
        max_b = 0
    if diff < min_diff:
        min_diff = diff
        min_b = 0
        
    if a_prev1 > 0:
        pos += 1
    elif a_prev1 < 0:
        neg += 1
        
    diff = pos - neg
    if diff > max_diff:
        max_diff = diff
        max_b = 1
    if diff < min_diff:
        min_diff = diff
        min_b = 1
        
    for n in range(limit-2):
        # n+2 is the index
        b = n + 2
        val = (a_prev1 ^ b) - a_prev2
        a_prev2 = a_prev1
        a_prev1 = val
        
        if val > 0:
            pos += 1
        elif val < 0:
            neg += 1
            
        diff = pos - neg
        if diff > max_diff:
            max_diff = diff
            max_b = b
        if diff < min_diff:
            min_diff = diff
            min_b = b
            
        if b % 100000000 == 0:
            print(f"Reached b={b}, max_diff so far: {max_diff}, min_diff so far: {min_diff}, current diff: {pos - neg}")
            
    print(f"Max diff: {max_diff} at b={max_b}")
    print(f"Min diff: {min_diff} at b={min_b}")
    print(f"Final diff: {pos - neg} at b={limit}")

solve()
