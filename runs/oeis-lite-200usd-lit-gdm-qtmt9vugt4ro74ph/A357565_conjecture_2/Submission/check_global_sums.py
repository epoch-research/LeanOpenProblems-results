import math

def choose(n, k):
    return math.comb(n, k)

def T(n, k):
    b = choose(n + k - 1, k)
    return 3 * b**2 + 2 * b**3

def check(p, r):
    n = p**r
    m = p**(r-1)
    modulus = p**(3*r + 3)
    
    # Sum over p not dividing k
    sum_non_div = 0
    for k in range(1, n + 1):
        if k % p != 0:
            sum_non_div += T(n, k)
            
    # Sum of differences for k divisible by p
    sum_diff = 0
    for j in range(1, m + 1):
        sum_diff += T(n, p*j) - T(m, j)
        
    print(f"p={p}, r={r}, modulus={modulus}:")
    print(f"  Sum over p \\nmid k mod modulus: {sum_non_div % modulus}")
    print(f"  Sum of differences mod modulus: {sum_diff % modulus}")
    print(f"  Total sum mod modulus: {(sum_non_div + sum_diff) % modulus}")

check(3, 2)
check(3, 3)
check(5, 2)
