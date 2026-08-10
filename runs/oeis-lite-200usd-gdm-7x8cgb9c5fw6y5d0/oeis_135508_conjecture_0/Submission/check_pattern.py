import math

def solve():
    MAX_N = 40000
    x = [0] * MAX_N
    x[0] = 0
    x[1] = 1
    for n in range(2, MAX_N):
        g = math.gcd(x[n-1], n)
        x[n] = x[n-1] * (2 + n // g)
        
    def is_prime(n):
        if n < 2: return False
        for i in range(2, int(math.sqrt(n))+1):
            if n % i == 0: return False
        return True
        
    for r in range(2, 200):
        if is_prime(r):
            # Find smallest k > 0 such that x[k] % r == 0
            k_list = [k for k in range(1, MAX_N) if x[k] % r == 0]
            if k_list:
                print(f"r = {r}: smallest k = {k_list[0]}, is k <= r^2-1? {k_list[0] <= r**2 - 1}, does r divide x(r^2-1)? {x[r**2-1] % r == 0 if r**2-1 < MAX_N else 'N/A'}")
            else:
                print(f"r = {r}: no k found up to {MAX_N}")

if __name__ == '__main__':
    solve()
