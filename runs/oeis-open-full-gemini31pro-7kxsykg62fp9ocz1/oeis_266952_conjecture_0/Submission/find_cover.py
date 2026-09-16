import sys

# Primes to use
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def solve(idx, current_cover, covered_count):
    if idx == len(primes):
        return False
        
    q = primes[idx]
    # We want to choose x mod q.
    # The classes covered by this prime will be {x, x+2} mod q.
    # But wait, we are trying to cover the Cartesian product of valid residues.
    # It's better to use SAT solver!
    pass
