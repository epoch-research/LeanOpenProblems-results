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
for n in range(1, 3000):
    an = a(n)
    pn = primorial(n, nth=False)
    if an == pn:
        solutions.append(n)

print("Total solutions up to 3000:", len(solutions))
for sol in solutions:
    # Check if sol is prime, or sol-1 is prime, etc.
    # Let's print the solutions
    pass
print("Solutions:", solutions)
