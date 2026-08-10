import math

def has_x_zero_solution(n):
    # We want to see if there exist a, b, c, d, y such that n = (2^a * 3^b)^2 + (2^c * 5^d)^2 + y^2
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
            if rem >= 0:
                # check if rem is a perfect square
                r = int(math.isqrt(rem))
                if r * r == rem:
                    return True
    return False

failed = []
for n in range(2, 1000):
    if n % 4 == 0:
        continue
    if not has_x_zero_solution(n):
        failed.append(n)
print(f"Failed numbers: {failed}")
