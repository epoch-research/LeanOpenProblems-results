def solve():
    a = [0]*100000
    a[0] = 0
    a[1] = 1
    for n in range(len(a)-2):
        # a[n+2] = xor(a[n+1], n+2) - a[n]
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    pos = 0
    neg = 0
    zero = 0
    for i in range(100000):
        if a[i] > 0:
            pos += 1
        elif a[i] < 0:
            neg += 1
        else:
            zero += 1
            
    print(f"Total: {len(a)}, Pos: {pos}, Neg: {neg}, Zero: {zero}")
    
    # Check if a[n+3] + a[n] is odd
    for n in range(100):
        val = a[n+3] + a[n]
        print(f"n={n}: a[n+3]+a[n]={val} (odd? {val % 2})")

solve()
