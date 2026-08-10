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

print("a(70) =", a(70))
print("primorial(70) =", primorial(70, nth=False))
print("Equal?", a(70) == primorial(70, nth=False))
