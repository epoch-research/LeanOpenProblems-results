from sympy import primorial, mobius, Rational

def check_up_to(max_n):
    total = Rational(0)
    solutions = []
    
    # Precompute primorials
    # primorial(n, nth=False) can be updated step by step:
    # if n is prime, mult by n.
    from sympy import isprime
    pn = 1
    
    for n in range(1, max_n + 1):
        if isprime(n):
            pn *= n
            
        mu = mobius(n)
        if mu == 1:
            total += Rational(n, 1)
        elif mu == -1:
            total += Rational(1, n)
        else:
            total += 1
            
        an = total.q
        if an == pn:
            solutions.append(n)
            
    print(f"Total solutions up to {max_n}: {len(solutions)}")
    print("Largest solutions:", solutions[-50:])

check_up_to(10000)
