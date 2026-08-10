def solve_R(p):
    p5 = p**5
    # R(k) - R(k-1) * k^2 / (p+k-1)^2 = 3 mod p^5
    # R(k) * (p+k-1)^2 - R(k-1) * k^2 = 3 * (p+k-1)^2 mod p^5
    # Let's fix R(0) and find R(1), ..., R(2*p)
    # We can do this because (p+k-1)^2 is coprime to p unless k = 1-p (mod p)
    # Wait, (p+k-1)^2 is coprime to p for all 1 <= k <= 2*p except:
    # k = p - 1 + 1 = p? No, p+k-1 is divisible by p when k = 1.
    # For k = 1: R(1) * p^2 - R(0) * 1 = 3 * p^2 mod p^5.
    # This determines R(0) mod p^2: R(0) = (R(1) - 3) * p^2 mod p^5.
    # In particular, R(0) must be divisible by p^2.
    # Let's try to search for R(0) in range(p^5) such that R(k) can be solved for all k.
    
    # Actually, let's just solve the system of linear equations for R(0), ..., R(2*p) mod p^5.
    # We have 2*p equations:
    # R(k) * (p+k-1)^2 - R(k-1) * k^2 = 3 * (p+k-1)^2 mod p^5 for k = 1, ..., 2*p.
    # There are 2*p + 1 variables: R(0), ..., R(2*p).
    # Let's use sympy to solve this linear system modulo p^5.
    import sympy as sp
    from sympy.matrices import Matrix
    
    eqs = []
    R = [sp.Symbol(f'R_{i}') for i in range(2 * p + 1)]
    for k in range(1, 2 * p + 1):
        eqs.append(R[k] * (p + k - 1)**2 - R[k-1] * k**2 - (p + k - 1)**2)
        
    sol = sp.solve(eqs, R)
    print("Solution with R_0 as free parameter:")
    for k in range(2 * p + 1):
        if R[k] in sol:
            print(f"  R_{k} = {sp.factor(sol[R[k]])}")
        else:
            print(f"  R_{k} is free")

solve_R(5)
