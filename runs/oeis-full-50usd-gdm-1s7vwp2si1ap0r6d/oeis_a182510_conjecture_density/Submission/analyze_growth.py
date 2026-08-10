def solve():
    limit = 100000
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    for i in [10, 100, 1000, 10000, 99999]:
        print(f"a[{i}] = {a[i]}")

solve()
