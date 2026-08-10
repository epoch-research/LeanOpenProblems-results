from sage.all import *

def find_recurrence():
    # Define variables
    n, k = var('n k')
    # Formula for the term
    # term = choose(n, k)^2 * choose(n+k, k) * choose(3n+2k, n)
    # Let's write a quick script to find the recurrence relation using Sage's ore_algebra or simply by guessing on the computed values!
    # Guessing a recurrence of order 2 or 3 is extremely easy using find_linear_recurrence or similar!
    vals = []
    for cur_n in range(12):
        total = 0
        for cur_k in range(cur_n + 1):
            term = (binomial(cur_n, cur_k) ** 2) * binomial(cur_n + cur_k, cur_k) * binomial(3 * cur_n + 2 * cur_k, cur_n)
            total += term
        vals.append(total)
    print("Values:")
    for i, v in enumerate(vals):
        print(f"a({i}) = {v}")
    
    # Let's find a recurrence relation
    # S(n) satisfies sum_{i=0}^d c_i(n) a(n+i) = 0
    # Let's try to find c_i(n) as polynomials in n.
    # We can do this using Sage's find_linear_relation or similar
    # or by solving a system of linear equations for the coefficients of the polynomials.
    # Let's assume order d = 2, max degree of polynomials deg = 3.
    # c_i(n) = \sum_{j=0}^{deg} c_{i,j} n^j
    d = 3
    deg = 5
    # We need enough values. For d=2, deg=4, we have 3 * 5 = 15 coefficients, we have 12 values, which might be a bit small.
    # Let's compute more values first.
    vals = []
    for cur_n in range(25):
        total = 0
        for cur_k in range(cur_n + 1):
            term = (binomial(cur_n, cur_k) ** 2) * binomial(cur_n + cur_k, cur_k) * binomial(3 * cur_n + 2 * cur_k, cur_n)
            total += term
        vals.append(total)
    
    # Solve system
    R = QQ['n']
    n_var = R.gen()
    
    # We want to find polynomials c_0(n), c_1(n), c_2(n) of degree <= deg
    # such that c_0(n) a(n) + c_1(n) a(n+1) + c_2(n) a(n+2) = 0
    # Let's set up the linear equations
    eqs = []
    vars_list = []
    for i in range(d + 1):
        for j in range(deg + 1):
            vars_list.append((i, j))
    
    # For each n from 0 to 22
    for cur_n in range(25 - d):
        row = []
        # The equation is \sum_{i=0}^d \sum_{j=0}^{deg} c_{i,j} cur_n^j a(cur_n + i) = 0
        eq_dict = {}
        for idx, (i, j) in enumerate(vars_list):
            coeff = (cur_n ** j) * vals[cur_n + i]
            eq_dict[idx] = coeff
        eqs.append(eq_dict)
    
    # Solve using Sage's Matrix
    M = matrix(QQ, len(eqs), len(vars_list))
    for r_idx, eq in enumerate(eqs):
        for c_idx, val in eq.items():
            M[r_idx, c_idx] = val
    
    # Find kernel
    K = M.right_kernel()
    print(f"Dimension of kernel: {K.dimension()}")
    for vec in K.basis():
        print("Found recurrence:")
        # Write as c_0(n) a(n) + c_1(n) a(n+1) + ...
        for i in range(d + 1):
            poly_terms = []
            for j in range(deg + 1):
                coef = vec[i * (deg + 1) + j]
                if coef != 0:
                    poly_terms.append(f"{coef} * n^{j}")
            poly_str = " + ".join(poly_terms)
            print(f"  c_{i}(n) = {poly_str}")

if __name__ == "__main__":
    find_recurrence()
