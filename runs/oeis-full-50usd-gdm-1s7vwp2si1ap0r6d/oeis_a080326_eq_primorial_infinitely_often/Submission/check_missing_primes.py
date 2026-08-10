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

for n in range(1, 200):
    an = a(n)
    pn = primorial(n, nth=False)
    missing = []
    for p in primerange(2, n + 1):
        if an % p != 0:
            missing.append(p)
    if missing:
        print(f"n = {n}: missing primes {missing}")
