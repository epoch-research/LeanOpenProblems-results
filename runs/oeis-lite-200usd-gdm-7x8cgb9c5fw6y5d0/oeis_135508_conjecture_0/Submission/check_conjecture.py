def solve():
    # We want to compute x_seq(n) modulo p.
    # x(0) = 0
    # x(1) = 1
    # x(n) = 2 * x(n-1) + lcm(x(n-1), n)
    # Since lcm(a, b) = a * b / gcd(a, b), we have:
    # x(n) = x(n-1) * (2 + n / gcd(x(n-1), n))
    
    # Let's find if there is any prime p such that p-2 is not prime, but p divides x(p-1).
    # Since we only care about whether p divides x(p-1), we can compute x(n) modulo p?
    # Wait, the recurrence for x(n) depends on gcd(x(n-1), n) as integers, so we cannot just work modulo p,
    # because gcd(x(n-1), n) depends on the exact integer value of x(n-1), not just modulo p.
    # But wait, gcd(x(n-1), n) is usually very small because it divides n.
    # Let's just compute the exact values of x(n) for n up to, say, 2000, and check.
    import math
    
    x = [0] * 10000
    x[0] = 0
    x[1] = 1
    for n in range(2, 10000):
        g = math.gcd(x[n-1], n)
        x[n] = x[n-1] * (2 + n // g)
        
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.sqrt(n))+1):
            if n % i == 0: return False
        return True
        
    print("Checking primes p up to 10000...")
    for p in range(2, 10000):
        if is_prime(p):
            if not is_prime(p-2):
                # check if p divides x(p-1)
                divides = (x[p-1] % p == 0)
                if divides:
                    print(f"COUNTEREXAMPLE FOUND: p = {p}, p-2 = {p-2} (not prime), but p divides x(p-1)")
                # else:
                #     print(f"p = {p} holds")
    print("Done checking.")

if __name__ == '__main__':
    solve()
