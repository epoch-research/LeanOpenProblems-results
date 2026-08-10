from sympy import primorial, mobius, Rational

def a(n):
    total = 0
    for k in range(1, n + 1):
        mu = mobius(k)
        if mu == 1:
            total += Rational(k, 1)
        elif mu == -1:
            total += Rational(1, k)
        else:
            total += 1
    return total.q

for k in range(1, 10):
    n = primorial(k, nth=False)
    an = a(n)
    pn = primorial(n, nth=False)
    print(f"k = {k}, n = {n}: an == pn? {an == pn}")
