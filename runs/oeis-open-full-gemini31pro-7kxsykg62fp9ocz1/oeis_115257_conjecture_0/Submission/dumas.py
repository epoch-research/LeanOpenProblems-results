import sympy

def v(p, n):
    res = 0
    while n >= p:
        n //= p
        res += n
    return res

def vp(p, k):
    return 2 * (v(p, 2*k) - 2 * v(p, k))

def check_dumas(n):
    for p in sympy.primerange(2, 2*n + 1):
        points = [vp(p, i) for i in range(n + 1)]
        v0, vn = points[0], points[n]
        is_line = True
        for i in range(1, n):
            if n * points[i] - n * v0 < (vn - v0) * i:
                is_line = False
                break
        if is_line and sympy.gcd(n, abs(vn - v0)) == 1:
            return p
    return None

def find_counter():
    for n in range(1, 100):
        if check_dumas(n) is None:
            print(f"n={n} has no Dumas prime for P_n")

find_counter()
