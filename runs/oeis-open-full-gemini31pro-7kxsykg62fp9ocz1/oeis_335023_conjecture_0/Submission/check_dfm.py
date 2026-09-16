import math

def A(n):
    if n < 2: return 0
    s = sum((-1)**k * math.factorial(n) // k for k in range(2, n+1))
    return math.gcd(s, math.factorial(n))

def a(n):
    return A(n+1) // A(n)

f = 0
m = 1
for k in range(1, 20):
    if k == 1:
        f = 0
        m = 1
    else:
        X = k * f + (1 if k % 2 == 0 else -1) * m
        Y = k * m
        d = math.gcd(X, Y)
        f = X // d
        m = Y // d
        print(f"k={k}, d={d}, f={f}, m={m}")

