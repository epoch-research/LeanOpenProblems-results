from sympy import binomial

for n in range(1, 10):
    val = sum(binomial(2*k, k)**2 / (k + 1) * (-1/2)**k for k in range(n+1))
    print(n, val)
