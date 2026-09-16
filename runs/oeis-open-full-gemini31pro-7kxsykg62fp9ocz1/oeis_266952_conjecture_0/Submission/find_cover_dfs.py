import sys

# Primes
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]

def find_cover():
    # We want to choose c_q for each q in primes.
    # The forbidden classes for p modulo q are 0, 2, c_q, c_q+2.
    # p is always 1 mod 6. We can just say p = 6k + 1.
    # Then p mod q = (6k+1) mod q.
    # 0, 2, c, c+2 mod q.
    # If p = 0 mod q => 6k+1 = 0 => 6k = -1 => k = -1/6 mod q
    # If p = 2 mod q => 6k+1 = 2 => 6k = 1 => k = 1/6 mod q
    # If p = c mod q => 6k+1 = c => k = (c-1)/6 mod q
    # If p = c+2 mod q => 6k+1 = c+2 => k = (c+1)/6 mod q
    
    # So for each q, we are forbidding 4 classes of k modulo q.
    # Two of them are FIXED: -1/6 and 1/6.
    # The other two are of the form x and x + 2/6 = x + 1/3 mod q.
    
    # We want to choose x for each q such that ALL integers k are covered.
    
    # Let's use a greedy approach to find a covering.
    # Or Z3.
    from z3 import Solver, Int, Or, And, sat
    
    P = primes[:15]
    print("Using primes:", P)
    s = Solver()
    
    x = {q: Int(f'x_{q}') for q in P}
    for q in P:
        s.add(x[q] >= 0, x[q] < q)
        
    # Is there a way to write this in Z3?
    # We can't write ForAll(k, ...) because Z3's nonlinear / periodic integer arithmetic is slow/incomplete.
    # BUT, we can just track the uncovered set of k modulo Product(P).
    pass
find_cover()
