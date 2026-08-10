from sympy import primorial, mobius, Rational, primerange

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

for p in primerange(11, 2000):
    if p % 30 in [7, 17, 23]:
        n = 6 * p
        an = a(n)
        pn = primorial(n, nth=False)
        if an == pn:
            print(f"p = {p} (n = {n}): solution")
        else:
            missing = [q for q in primerange(2, n+1) if an % q != 0]
            print(f"p = {p} (n = {n}): NOT solution, missing {missing}")
