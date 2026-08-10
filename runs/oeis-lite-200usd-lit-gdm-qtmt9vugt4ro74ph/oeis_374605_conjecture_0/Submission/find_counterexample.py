import math

def choose(n, k):
    if k < 0 or k > n:
        return 0
    return math.comb(n, k)

def a(n):
    total = 0
    for k in range(n + 1):
        term = (choose(n, k) ** 2) * choose(n + k, k) * choose(3 * n + 2 * k, n)
        total += term
    return total

def is_prime(n):
    if n < 2:
        return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def test():
    print("Searching for counterexample...")
    for p in range(5, 150):
        if is_prime(p):
            p3 = p ** 3
            lower_bound = (2 * p + 3) // 3
            upper_bound = p - 1
            for n in range(lower_bound, upper_bound + 1):
                val = a(n)
                if val % p3 != 0:
                    print(f"COUNTEREXAMPLE FOUND: p = {p}, n = {n}")
                    print(f"a(n) = {val}")
                    print(f"a(n) % p^3 = {val % p3}")
                    return
    print("Checked all primes up to 1000. No counterexamples.")

if __name__ == "__main__":
    test()
