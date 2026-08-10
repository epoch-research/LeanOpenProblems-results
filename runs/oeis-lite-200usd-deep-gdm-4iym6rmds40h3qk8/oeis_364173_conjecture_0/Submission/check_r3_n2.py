import sympy

memo = {}

def get_a(n):
    if n in memo:
        return memo[n]
    if n == 0:
        res = 1
    elif n % 2 == 0:
        k = n // 2
        res = int(sympy.factorial(18*k) * sympy.factorial(4*k) * sympy.factorial(3*k) / (sympy.factorial(9*k) * sympy.factorial(8*k) * sympy.factorial(6*k) * sympy.factorial(2*k)))
    else:
        k = (n - 1) // 2
        res = int(sympy.factorial(4*k+2) * sympy.factorial(9*k+4) / (sympy.factorial(8*k+4) * sympy.factorial(2*k+1) * sympy.factorial(3*k+1)) * (2**(12*k+6)))
    memo[n] = res
    return res

v1 = get_a(2 * 5**3)
v2 = get_a(2 * 5**2)
mod = 5**9
diff = v1 - v2
print(f"p=5, n=2, r=3: {diff % mod == 0} (diff % mod = {diff % mod})")
