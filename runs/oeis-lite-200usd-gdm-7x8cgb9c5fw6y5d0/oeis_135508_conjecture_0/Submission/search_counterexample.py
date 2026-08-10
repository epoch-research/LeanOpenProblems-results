import math

def solve():
    MAX_P = 150000
    x = [0] * MAX_P
    x[0] = 0
    x[1] = 1
    for n in range(2, MAX_P):
        g = math.gcd(x[n-1], n)
        x[n] = x[n-1] * (2 + n // g)
        
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.sqrt(n))+1):
            if n % i == 0: return False
        return True
        
    print("Searching for counterexample up to 150,000...")
    for p in range(2, MAX_P):
        if is_prime(p):
            if not is_prime(p-2):
                # check if p divides x(p-1)
                divides = (x[p-1] % p == 0)
                if divides:
                    print(f"COUNTEREXAMPLE FOUND: p = {p}, p-2 = {p-2} (not prime), but p divides x(p-1)!")
                    return
    print("No counterexample found.")

if __name__ == '__main__':
    solve()
