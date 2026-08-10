def solve():
    limit = 1000000
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    exceptions = []
    for n in range(limit):
        if abs(a[n]) <= 2*n + 5:
            exceptions.append((n, a[n]))
            
    print(f"Total exceptions: {len(exceptions)}")
    print(f"First 50 exceptions: {exceptions[:50]}")
    if len(exceptions) > 50:
        print(f"Last 50 exceptions: {exceptions[-50:]}")

solve()
