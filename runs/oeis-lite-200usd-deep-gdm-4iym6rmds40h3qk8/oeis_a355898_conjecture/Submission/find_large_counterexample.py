import math

def search():
    # We want to find any n >= 3774 such that gcd(a[n-1], a[n-2]) > 1.
    prev2 = 1 # a[1]
    prev1 = 1 # a[2]
    
    # We can pre-allocate or just use variables
    for n in range(3, 4000):
        g = math.gcd(prev1, prev2)
        curr = g + (prev1 + prev2) // g
        if n >= 3774 and g > 1:
            print(f"COUNTEREXAMPLE FOUND: n = {n}, gcd = {g}")
            return
        prev2 = prev1
        prev1 = curr
        
    print("No counterexample found up to 500,000.")

search()
