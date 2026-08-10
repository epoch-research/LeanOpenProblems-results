import math

def is_sum2(n):
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

def has_sol(n):
    # We want to see if we can find a, b, c, d such that n - (2^a * 3^b)^2 - (2^c * 5^d)^2 is a sum of two squares.
    # We don't restrict a, b, c, d except by the natural limit val^2 <= n.
    S1 = []
    a = 0
    while True:
        p2 = 2**a
        if p2**2 > n:
            break
        b = 0
        while True:
            val = p2 * (3**b)
            if val**2 > n:
                break
            S1.append(val**2)
            b += 1
        a += 1
    
    S2 = []
    c = 0
    while True:
        p2 = 2**c
        if p2**2 > n:
            break
        d = 0
        while True:
            val = p2 * (5**d)
            if val**2 > n:
                break
            S2.append(val**2)
            d += 1
        c += 1

    for t1 in S1:
        for t2 in S2:
            rem = n - t1 - t2
            if rem >= 0 and is_sum2(rem):
                return True
    return False

print(f"5215135 has solution? {has_sol(5215135)}")
print(f"9990895 has solution? {has_sol(9990895)}")
