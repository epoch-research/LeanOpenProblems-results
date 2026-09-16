def b_A145062(k):
    if k == 0:
        return 1
    if k % 2 == 0:
        return k // 2 + 1
    else:
        return 0

memo = {}
def A145062_aux(n, k):
    if n == 0:
        return 1 if k == 0 else 0
    if k > n:
        return 0
    if (n, k) in memo:
        return memo[(n, k)]
    
    res = A145062_aux(n-1, k+1)
    if k > 0:
        res += A145062_aux(n-1, k-1)
    res += b_A145062(k) * A145062_aux(n-1, k)
    
    memo[(n, k)] = res
    return res

def a(n):
    return A145062_aux(n, 0)

for i in range(20):
    print(a(i), end=', ')
print()
