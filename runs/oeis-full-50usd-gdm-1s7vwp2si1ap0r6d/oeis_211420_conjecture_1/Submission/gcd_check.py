import math

def check(r):
    print(f"--- r = {r} ---")
    for n in range(1, 40):
        d = 8 * n - (2 * r + 1)
        if d <= 0:
            continue
        Y = math.factorial(4 * n) * math.factorial(3 * n) * math.factorial(2 * n)
        g = math.gcd(d, Y)
        print(f"n={n}: d={d}, gcd(d, Y)={g}")

check(1)
check(2)
