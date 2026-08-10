from sympy import binomial

def a108625_aux(n, k):
    ans = 0
    for i in range(k + 1):
        ans += binomial(n, i)**2 * binomial(n + k - i, k - i)
    return ans

def A376462(n):
    ans = 0
    for k in range(n + 1):
        ans += binomial(n, k)**2 * binomial(n + k, k) * a108625_aux(n, n - k)
    return ans

terms = [A376462(n) for n in range(10)]
print(terms)
