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

for n in range(1, 100):
    an = a(n)
    pn = primorial(n)
    if an == pn:
        print(f"n = {n}: EQUAL = {an}")
    else:
        print(f"n = {n}: a(n) = {an}, primorial = {pn}")
