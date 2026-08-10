def solve():
    limit = 100000000
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    pos = 0
    neg = 0
    max_diff = -1
    min_diff = 1000000
    
    for b in range(limit):
        diff = pos - neg
        if diff > max_diff:
            max_diff = diff
            max_b = b
        if diff < min_diff:
            min_diff = diff
            min_b = b
        
        val = a[b]
        if val > 0:
            pos += 1
        elif val < 0:
            neg += 1
            
    print(f"Max diff: {max_diff} at b={max_b}")
    print(f"Min diff: {min_diff} at b={min_b}")
    print(f"Final diff: {pos - neg} at b={limit}")

solve()
