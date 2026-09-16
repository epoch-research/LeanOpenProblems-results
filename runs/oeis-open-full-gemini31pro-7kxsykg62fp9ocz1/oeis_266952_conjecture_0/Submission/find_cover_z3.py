from z3 import *

# Try with first few primes
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def find_cover(num_primes):
    P = primes[:num_primes]
    print(f"Trying with primes {P}")
    
    # n_q is the choice of n mod q
    n_vars = {q: Int(f'n_{q}') for q in P}
    
    s = Solver()
    for q in P:
        s.add(n_vars[q] >= 0, n_vars[q] < q)
        
    # We want to ensure that for EVERY p from 0 to Prod(P)-1, 
    # there is SOME q in P such that p is in F_q.
    # This is equivalent to saying there is NO p such that for all q in P, p not in F_q.
    
    # Since Prod(P) is too large, we can't iterate over all p.
    # But wait, p mod q is independent for each q!
    # So if there is ANY valid p, it means we can pick p_q not in F_q for each q.
    # We want to PREVENT this!
    # That means for ANY choice of n_q, there exists some p_q... NO!
    # A covering system exists iff there are choices of n_q such that the remaining classes for p_q are EMPTY.
    # But remaining classes for p_q are independent!
    # The number of remaining classes mod q is q - |F_q|.
    # The total number of valid p modulo Prod(q) is Prod (q - |F_q|).
    # For this to be zero, AT LEAST ONE of the factors must be zero!
    pass
