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

def test():
    primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    for p in primes:
        p3 = p ** 3
        lower_bound = (2 * p + 3) // 3
        upper_bound = p - 1
        for n in range(lower_bound, upper_bound + 1):
            val = a(n)
            if val % p3 != 0:
                print(f"COUNTEREXAMPLE: p = {p}, n = {n}, a(n) = {val}, a(n) % p^3 = {val % p3}")
                return
    print("No counterexamples found for primes up to 100!")

if __name__ == "__main__":
    test()
