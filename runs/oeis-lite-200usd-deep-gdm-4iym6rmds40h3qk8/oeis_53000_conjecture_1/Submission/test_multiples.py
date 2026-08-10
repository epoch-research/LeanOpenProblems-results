import sympy

def check_selective():
    # Let's check n which are multiples of 30
    print("Checking multiples of 30...")
    for k in range(1, 100000):
        n = 30 * k
        phi = sympy.totient(n)
        limit = n**2 + 1 + phi
        p = sympy.nextprime(n**2)
        if p > limit:
            print(f"COUNTEREXAMPLE FOUND! n = {n}")
            print(f"phi(n) = {phi}")
            print(f"A053000(n) = {p - n**2}")
            return
    print("Checked multiples of 30 up to 30 * 100000")

    # Let's check n which are multiples of 210
    print("Checking multiples of 210...")
    for k in range(1, 100000):
        n = 210 * k
        phi = sympy.totient(n)
        limit = n**2 + 1 + phi
        p = sympy.nextprime(n**2)
        if p > limit:
            print(f"COUNTEREXAMPLE FOUND! n = {n}")
            print(f"phi(n) = {phi}")
            print(f"A053000(n) = {p - n**2}")
            return
    print("Checked multiples of 210 up to 210 * 100000")

check_selective()
