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

v1 = get_a(5**4) # a(625)
v2 = get_a(5**3) # a(125)
mod = 5**12
diff = v1 - v2
print(f"p=5, n=1, r=4: {diff % mod == 0} (diff % mod = {diff % mod})")
