from z3 import *

def check_cover(max_p):
    primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79][:max_p]
    print("Primes:", primes)
    
    # We want to find if there exists a choice of c_q for q in primes
    # such that NO x is valid for all q.
    # An x is valid for q if x != 0, 2, c_q, c_q+2 mod q.
    # So for each x, there is some q where x in {0, 2, c_q, c_q+2} mod q.
    # This is equivalent to: we can cover all x.
    # Wait, we can't iterate over all x from 0 to Prod(primes) - 1.
    # But we can use Z3 to find (c_q) such that ForAll x, Or(x covered by q).
    
    # Let's write this in Z3 using integers.
    s = Solver()
    c = {q: Int(f'c_{q}') for q in primes}
    for q in primes:
        s.add(c[q] >= 0, c[q] < q)
        
    x = Int('x')
    
    # For a given x and q, is x covered?
    def covered(x, q):
        xq = x % q
        return Or(xq == 0, xq == 2, xq == c[q], xq == (c[q] + 2) % q)
        
    # Condition: For all x, Or_{q} covered(x, q)
    # Since x is an integer, we can just say ForAll x in 0 .. Prod-1
    # Z3 can handle ForAll.
    s.add(ForAll(x, Or([covered(x, q) for q in primes])))
    
    print("Solving...")
    res = s.check()
    print("Result:", res)

check_cover(8)
