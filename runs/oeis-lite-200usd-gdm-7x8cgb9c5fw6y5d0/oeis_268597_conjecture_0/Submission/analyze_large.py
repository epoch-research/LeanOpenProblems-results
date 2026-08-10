import sympy

def find_witness(n):
    for x in range(1, 100000):
        if (x - 1) % sympy.totient(x) == n:
            return x
    return None

print("Analyzing witnesses for composite m >= 501:")
count = 0
for m in range(501, 600):
    if not sympy.isprime(m):
        n = m - 1
        x = find_witness(n)
        if x:
            factors = sympy.factorint(x)
            factor_str = " * ".join([f"{pr}^{ext}" for pr, ext in factors.items()])
            # check relationship with m
            # Is x of the form A * p where p is prime and A is a divisor of some small number?
            # Or can we write x - m in some simple way?
            print(f"m = {int(m):3d} (factors={sympy.factorint(m)}): x = {int(x):6d} = {str(factor_str):20s}, phi(x) = {int(sympy.totient(x)):5d}, k = {int((x-1)//sympy.totient(x))}")
            count += 1
