import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for j in [0, 1, 2]:
    for s in [0, 1, 2]:
        for deg in range(5):
            coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
            N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
            N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
            
            lhs = N_k * (p+k-1)**s * (p+k-1)**2 - N_k_minus_1 * (p+k)**s * k**2
            rhs = 3 * p**j * (p+k)**s * (p+k-1)**s * (p+k-1)**2
            num = sp.expand(lhs - rhs)
            
            # We want num to be divisible by p^3.
            # So num mod p^3 must be 0 for all k.
            # This means the coefficients of num with respect to k must be divisible by p^3.
            diff = sp.poly(num, k)
            eqs = [c % p**3 for c in diff.coeffs()]
            
            sol = sp.solve(diff.coeffs(), coeffs) # let's first solve exactly
            if sol:
                print(f"Exact solution: j={j}, s={s}, deg={deg}:")
                print(f"  R(k) = {sp.factor((N_k / (p**j * (p+k)**s)).subs(sol))}")
                
            # Now let's try to solve modulo p^3
            # We can do this by substituting p with a prime or solving in the ring Z/p^3Z.
            # Let's see if we can find a solution for a specific p first, e.g. p=5, mod 125.
            
print("Done.")
