def solve():
    limit = 999996
    a = [0]*limit
    a[0] = 0
    a[1] = 1
    for n in range(limit-2):
        a[n+2] = (a[n+1] ^ (n+2)) - a[n]
    
    both_pos = 0
    both_neg = 0
    pos_neg = 0
    neg_pos = 0
    zero_other = 0
    
    for n in range(limit):
        if n % 6 < 3:
            fn = n + 3
            val_n = a[n]
            val_fn = a[fn]
            if val_n > 0 and val_fn > 0:
                both_pos += 1
            elif val_n < 0 and val_fn < 0:
                both_neg += 1
            elif val_n > 0 and val_fn < 0:
                pos_neg += 1
            elif val_n < 0 and val_fn > 0:
                neg_pos += 1
            else:
                zero_other += 1
                
    print(f"both_pos: {both_pos}")
    print(f"both_neg: {both_neg}")
    print(f"pos_neg (a_n > 0, a_fn < 0): {pos_neg}")
    print(f"neg_pos (a_n < 0, a_fn > 0): {neg_pos}")
    print(f"zero_other: {zero_other}")
    print(f"Total pairs: {limit // 2}")

solve()
