def is_square(k):
    import math
    s = int(math.isqrt(k))
    return s*s == k

def solve(n):
    # Search for x, y, z, w such that:
    # x^2 + y^2 + z^2 + w^2 = n
    # x >= y >= 0, z >= 0, w >= 0
    # x^2 + 8y^2 + 16z^2 is a square
    import math
    limit = int(math.isqrt(n)) + 1
    for x in range(limit):
        for y in range(x + 1):
            for z in range(limit):
                rem = n - (x**2 + y**2 + z**2)
                if rem < 0:
                    continue
                w = int(math.isqrt(rem))
                if w*w == rem:
                    if is_square(x**2 + 8*y**2 + 16*z**2):
                        return (x, y, z, w)
    return None

for n in range(1, 200):
    if n % 4 != 0:
        sol = solve(n)
        if sol is None:
            print(f"No solution for {n}!")
            break
else:
    print("All n up to 200 have a solution!")
