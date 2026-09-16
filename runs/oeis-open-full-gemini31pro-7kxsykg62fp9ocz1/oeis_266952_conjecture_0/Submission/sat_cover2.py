from z3 import *

primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]

def check_cover(k):
    P = primes[:k]
    print(f"\n--- Checking for k={k}, primes={P} ---")
    s = Solver()
    
    # c[q] is the choice of 6n mod q
    c = {q: Int(f'c_{q}') for q in P}
    for q in P:
        s.add(c[q] >= 0, c[q] < q)
        
    # We want to cover all x in 0 .. Prod(P)-1
    # Actually, we can use the integer logic: 
    # ForAll x, Or_{q} (x%q == 0 or x%q == 2 or x%q == c_q or x%q == c_q+2)
    # BUT Z3's ForAll with mod is slow.
    # Alternative: use bitvectors? Still slow.
    
    # Better alternative: backtracking in Python!
    pass

