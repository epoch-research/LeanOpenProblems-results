memo = {}
def b(k):
    if k == 0: return 1
    if k % 2 == 0: return k // 2 + 1
    return 0

def A(n, k):
    if n == 0: return 1 if k == 0 else 0
    if k > n or k < 0: return 0
    if (n, k) in memo: return memo[(n, k)]
    res = A(n-1, k+1)
    if k > 0: res += A(n-1, k-1)
    res += b(k) * A(n-1, k)
    memo[(n, k)] = res
    return res

def a(n): return A(n, 0)

for i in range(20):
    print(a(i), end=', ')
print()
