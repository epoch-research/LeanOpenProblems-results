import sys

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

def get_F(q, n):
    F = {0, 2, (6*n)%q, (6*n+2)%q}
    return F

def solve():
    # We will use Z3 to find a covering system.
    pass
