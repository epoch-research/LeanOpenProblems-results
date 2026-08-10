import math

def nCr(n, r):
    return math.comb(n, r)

# b_1(n) = nCr(2n-1, n)
def b_1(n):
    return nCr(2 * n - 1, n)

n1 = 2 * 125
n2 = 2 * 25
val1 = b_1(n1)
val2 = b_1(n2)
mod = 5 ** 9
diff = val1 - val2
print("diff % mod =", diff % mod)
