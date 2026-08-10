from sympy import primorial, mobius, Rational, isprime

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

def f(x):
    count = 0
    for m in range(1, x + 1):
        if m % 2 != 0 and mobius(m) == 1:
            count += 1
    return count

for p in range(2, 500):
    if isprime(p):
        fp = f(p // 2)
        an = a(p)
        pn = primorial(p, nth=False)
        if an == pn:
            print(f"p = {p}: f(p//2) = {fp}, equal = True")
        else:
            # check which primes are missing from a(p)
            missing = []
            for q in range(2, p + 1):
                if isprime(q) and an % q != 0:
                    missing.append(q)
            print(f"p = {p}: f(p//2) = {fp}, equal = False, missing = {missing}")
