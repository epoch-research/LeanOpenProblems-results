import math

def is_sum_of_two_squares(n):
    if n < 0:
        return False
    temp = n
    while temp % 2 == 0:
        temp //= 2
    d = 3
    while d * d <= temp:
        if temp % d == 0:
            count = 0
            while temp % d == 0:
                count += 1
                temp //= d
            if d % 4 == 3 and count % 2 != 0:
                return False
        d += 2
    if temp > 1 and temp % 4 == 3:
        return False
    return True

def has_restricted_solution(n, max_exp):
    # a, b, c, d <= max_exp
    S1_vals = []
    for a in range(max_exp + 1):
        for b in range(max_exp + 1):
            val = (2**a) * (3**b)
            if val**2 <= n:
                S1_vals.append(val**2)
    S2_vals = []
    for c in range(max_exp + 1):
        for d in range(max_exp + 1):
            val = (2**c) * (5**d)
            if val**2 <= n:
                S2_vals.append(val**2)
                
    for t1 in S1_vals:
        for t2 in S2_vals:
            rem = n - t1 - t2
            if rem >= 0 and is_sum_of_two_squares(rem):
                return True
    return False

for max_exp in [1, 2, 3]:
    print(f"Checking max_exp = {max_exp}")
    failed = []
    for n in range(2, 50000):
        # We only care about n not divisible by 4, since n divisible by 4 can be reduced by 4
        if n % 4 == 0:
            continue
        if not has_restricted_solution(n, max_exp):
            failed.append(n)
            if len(failed) > 10:
                break
    if not failed:
        print(f"Success for max_exp = {max_exp} up to 50,000!")
    else:
        print(f"Failed for max_exp = {max_exp}. Some failures: {failed}")
