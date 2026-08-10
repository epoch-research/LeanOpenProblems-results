import math

def solve():
    MAX_N = 20000
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
        
    for r in range(2, 120):
        if is_prime(r):
            k_list = [k for k in range(1, MAX_N) if x[k] % r == 0]
            if k_list:
                k0 = k_list[0]
                bound = r**2 - 1
                print(f"r = {r:3d}: smallest k = {k0:5d}, r^2-1 = {bound:5d}, ratio = {k0/bound:.4f}, holds? {k0 <= bound}")
            else:
                print(f"r = {r:3d}: no k found up to {MAX_N}")

if __name__ == '__main__':
    solve()
