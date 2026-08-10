import sympy

def phi(n):
    return sympy.totient(n)

def find_witness(n):
    # We want x > 0 such that (x - 1) % phi(x) == n
    # Let's search for x of the form...
    # Let's see all x that work for a given n
    for x in range(1, 100000):
        if (x - 1) % phi(x) == n:
            return x
    return None

# Let's print the smallest witness x for some composite m = n + 1
print("m, n, factors, witness x, phi(x), (x-1)/phi(x)")
for m in range(4, 100):
    if not sympy.isprime(m):
        n = m - 1
        x = find_witness(n)
        if x:
            print(f"m={int(m):2d}, n={int(n):2d}, factors={sympy.factorint(m)}, x={int(x):5d}, phi(x)={int(phi(x)):5d}, k={int((x-1)//phi(x))}")
        else:
            print(f"m={m:2d}, n={n:2d}, factors={sympy.factorint(m)}, no witness < 100000")
