from sympy import primorial, mobius, Rational, primerange
def check(n):
    total = 0
    for k in range(1, n + 1):
        mu = mobius(k)
        if mu == 1:
            total += Rational(k, 1)
        elif mu == -1:
            total += Rational(1, k)
        else:
            total += 1
    an = total.q
    missing = [p for p in primerange(2, n+1) if an % p != 0]
    return missing

for p in primerange(11, 200):
    n = 6 * p
    print(f"p = {p} (n = {n}): missing {check(n)}")
