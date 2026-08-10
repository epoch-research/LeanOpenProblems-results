import sympy, math

def sigma(n):
    ans = 0
    for i in range(1, int(math.sqrt(n)) + 1):
        if n % i == 0:
            ans += i
            if i * i != n:
                ans += n // i
    return ans

def A_and_b(g):
    s = sigma(g)
    gcd = math.gcd(s, g)
    a = s // gcd
    b = g // gcd
    return a - b, b, a

def solve_n(n):
    print(f"Searching for n = {n}...")
    # Case 1: i = q * g where q is prime, q not divide g
    # We need A(g) to divide n - 1
    divisors = []
    for d in range(1, int(math.sqrt(n - 1)) + 1):
        if (n - 1) % d == 0:
            divisors.append(d)
            if d * d != n - 1:
                divisors.append((n - 1) // d)
    
    print(f"Divisors of {n-1}: {divisors}")
    
    # We search for g such that A(g) is in divisors
    # Let's search g up to 1,000,000
    for g in range(1, 10000000):
        val, b, a = A_and_b(g)
        if val in divisors:
            k = (n - 1) // val
            p = k * b - 1
            if p > 1 and sympy.isprime(p) and g % p != 0 and math.gcd(k * a, p) == 1:
                print(f"Found Case 1: g = {g}, p = {p}, i = {g * p}")
                return g * p
                
    # Case 2: q | g. i = q^(r+1) * m, where q is prime, q not divide m.
    # We need q^r to divide sigma(m).
    # Since r >= 1, and q is prime, let's test r from 1 to 5, q up to 100000
    # and m such that sigma(m) is a multiple of q^r.
    # Actually, let's write a direct search for i = q^(r+1) * m
    # where r >= 1, and we check the relation.
    # To do this efficiently, we can loop over m, then find possible q.
    print("No Case 1 solution found up to g = 10,000,000. Trying other structures...")
    return None

solve_n(203)
