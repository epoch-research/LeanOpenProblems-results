import math

def val_p(x, p):
    if x == 0:
        return float('inf')
    val = 0
    while x % p == 0:
        val += 1
        x //= p
    return val

def choose(n, k):
    return math.comb(n, k)

def T(n, k):
    b = choose(n + k - 1, k)
    return 3 * b**2 + 2 * b**3

def check(p, r):
    n = p**r
    m = p**(r-1)
    target = 3 * r + 3
    print(f"--- p={p}, r={r}, target={target} ---")
    
    # 1. Check T(n, k) for p not dividing k
    min_val_non_div = float('inf')
    for k in range(1, n + 1):
        if k % p != 0:
            val = val_p(T(n, k), p)
            if val < min_val_non_div:
                min_val_non_div = val
    print(f"Min valuation of T(n, k) for p \\nmid k: {min_val_non_div}")
    
    # 2. Check T(n, pj) - T(m, j) for each j
    min_val_diff = float('inf')
    for j in range(1, m + 1):
        diff = T(n, p*j) - T(m, j)
        val = val_p(diff, p)
        if val < min_val_diff:
            min_val_diff = val
        print(f"  j={j}: val(T(n, pj) - T(m, j)) = {val}")
    print(f"Min valuation of difference: {min_val_diff}")

check(3, 2)
check(3, 3)
check(5, 2)
