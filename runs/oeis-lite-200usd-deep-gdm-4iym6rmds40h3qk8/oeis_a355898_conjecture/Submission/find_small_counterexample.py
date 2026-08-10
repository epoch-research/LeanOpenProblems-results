import math
import sys

def solve():
    # We want to compute A355898 up to some limit.
    # Since we only care about gcd(a(n-1), a(n-2)), we can just compute it.
    # A355898: a(1) = 1, a(2) = 1.
    # a(n) = g + (a(n-1) + a(n-2)) / g, where g = gcd(a(n-1), a(n-2)).
    
    prev2 = 1
    prev1 = 1
    
    for n in range(3, 1000000): # 1 million
        g = math.gcd(prev1, prev2)
        if g > 1:
            # We don't return here so we can find a counterexample >= 3775
            pass
        curr = g + (prev1 + prev2) // g
        
        # Check if the formula holds
        if n >= 3775:
            if curr != 1 + prev1 + prev2:
                print(f"ACTUAL COUNTEREXAMPLE FOR THE CONJECTURE! at n = {n}")
                print(f"A355898({n}) = {curr}")
                print(f"1 + A355898({n-1}) + A355898({n-2}) = {1 + prev1 + prev2}")
                print(f"gcd(A355898({n-1}), A355898({n-2})) = {g}")
                return
                
        prev2 = prev1
        prev1 = curr
        
        if n % 10000000 == 0:
            print(f"Reached n = {n}", flush=True)

solve()
