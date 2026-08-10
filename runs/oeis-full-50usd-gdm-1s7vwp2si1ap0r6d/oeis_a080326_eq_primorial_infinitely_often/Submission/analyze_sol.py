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

solutions = []
for n in range(1, 1000):
    an = a(n)
    pn = primorial(n, nth=False)
    if an == pn:
        solutions.append(n)

print("Number of solutions:", len(solutions))
print("Solutions:", solutions[:100])
