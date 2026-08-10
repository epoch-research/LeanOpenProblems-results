import math

def choose(n, k):
    if k < 0 or k > n:
        return 0
    return math.comb(n, k)

def test():
    primes = [5, 7, 11, 13, 17, 19, 23, 29]
    for p in primes:
        p3 = p ** 3
        lower_bound = (2 * p + 3) // 3
        upper_bound = p - 1
        print(f"p = {p}")
        for n in range(lower_bound, upper_bound + 1):
            all_divisible = True
            for k in range(n + 1):
                term = (choose(n, k) ** 2) * choose(n + k, k) * choose(3 * n + 2 * k, n)
                if term % p3 != 0:
                    all_divisible = False
                    print(f"  n = {n}, k = {k}: term = {term}, term % p^3 = {term % p3}")
            if all_divisible:
                print(f"  n = {n}: All terms are divisible by p^3!")

if __name__ == "__main__":
    test()
