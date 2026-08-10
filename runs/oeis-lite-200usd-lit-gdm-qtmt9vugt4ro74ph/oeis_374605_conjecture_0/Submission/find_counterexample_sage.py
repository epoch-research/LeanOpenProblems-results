from sage.all import *

def is_prime(n):
    if n < 2:
        return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def test():
    print("Searching for counterexample using Sage...")
    for p in range(5, 500):
        if is_prime(p):
            p3 = p ** 3
            lower_bound = (2 * p + 3) // 3
            upper_bound = p - 1
            for n in range(lower_bound, upper_bound + 1):
                # Compute sum modulo p^3
                total = 0
                for k in range(n + 1):
                    # compute (binomial(n, k)^2 * binomial(n+k, k) * binomial(3*n+2*k, n)) % p3
                    c1 = binomial(n, k)
                    c2 = binomial(n + k, k)
                    c3 = binomial(3 * n + 2 * k, n)
                    term = (c1 * c1 * c2 * c3) % p3
                    total = (total + term) % p3
                if total != 0:
                    print(f"COUNTEREXAMPLE FOUND: p = {p}, n = {n}, total % p^3 = {total}")
                    return
            if p % 20 == 0 or p in [11, 23, 43, 73, 107]:
                print(f"Checked up to p = {p}")
    print("Checked all primes up to 500. No counterexamples.")

if __name__ == "__main__":
    test()
