import sympy

def find_counterexample(start, end):
    print(f"Searching from {start} to {end}...")
    for n in range(start, end):
        phi = sympy.totient(n)
        limit = n**2 + 1 + phi
        # We want to check if the next prime after n^2 is > limit
        p = sympy.nextprime(n**2)
        if p > limit:
            print(f"COUNTEREXAMPLE FOUND! n = {n}")
            print(f"n^2 = {n**2}")
            print(f"phi(n) = {phi}")
            print(f"next_prime = {p}")
            print(f"A053000(n) = {p - n**2}")
            print(f"1 + phi(n) = {1 + phi}")
            return n
    print("Done search.")
    return None

find_counterexample(4, 100000)
