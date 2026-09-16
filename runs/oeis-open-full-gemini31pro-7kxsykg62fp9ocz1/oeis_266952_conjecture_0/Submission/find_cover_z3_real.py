from z3 import *
import sys

# Primes available:
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def try_cover(k):
    P = primes[:k]
    print(f"Trying to cover with {k} primes: {P}")
    s = Solver()
    
    # c_q is the residue of 6n mod q
    c = {q: Int(f'c_{q}') for q in P}
    for q in P:
        s.add(c[q] >= 0, c[q] < q)
        
    # We want to cover all integers x.
    # Actually, we only need to cover x which are not covered by 2 and 3.
    # Mod 2, x=0 and x=2 are covered by 0. So x=1 is left.
    # Mod 3, x=0 and x=2 are covered. So x=1 is left.
    # By CRT, mod 6, x must be 1 mod 2 and 1 mod 3, so x = 1 mod 6.
    #Wait, x is p, which is prime. Primes are 1 or 5 mod 6 (except 2,3).
    # But wait, mod 2: forbidden are x=0, x=2. (so x must be 1 mod 2).
    # mod 3: forbidden are x=0, x=2. (so x must be 1 mod 3).
    # Wait, 1 mod 2 and 1 mod 3 means x = 1 mod 6!
    # Wait! Mod 3, x=0 means p is divisible by 3. x=2 means p-2 is divisible by 3 (so p=2 mod 3).
    # So the ONLY allowed value for p mod 3 is p=1 mod 3.
    # And mod 2, the ONLY allowed value is p=1 mod 2.
    # Therefore, ANY prime p that satisfies the conditions MUST be p = 1 mod 6 !
    #Wait! p=7 is 1 mod 6. p-2 = 5.
    # p=13 is 1 mod 6. p-2 = 11.
    # p=19 is 1 mod 6. p-2 = 17.
    # Yes! All twin prime larger than 3 are 1 mod 6.
    # So x is ALREADY covered for all x != 1 mod 6.
    # So we only need to cover x = 1 mod 6 using the primes in P!
    
    # We can use a recursive search or Z3.
    # To use Z3:
    # A set of c_q covers all x = 1 mod 6 iff there is no x = 1 mod 6 such that for all q in P, x != 0, 2, c_q, c_q+2 mod q.
    # Since x is an integer, and the condition is periodic with period 6*Prod(P),
    # this is equivalent to saying there is no such x in 0..6*Prod(P)-1.
    pass

try_cover(5)
