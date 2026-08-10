import sympy

def totient(n):
    return sympy.totient(n)

def next_prime(n2):
    return sympy.nextprime(n2)

def A053000(n):
    return next_prime(n**2) - n**2

def check(limit):
    for n in range(1, limit + 1):
        a = A053000(n)
        phi = totient(n)
        if a > 1 + phi:
            print(f"COUNTEREXAMPLE FOUND: n={n}, A053000(n)={a}, 1+phi(n)={1+phi}")
            return n
    print(f"Checked up to {limit}, no counterexamples.")
    return None

check(100000)
