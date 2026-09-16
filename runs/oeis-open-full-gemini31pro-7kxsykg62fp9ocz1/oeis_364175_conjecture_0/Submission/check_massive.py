import math
import sys
import multiprocessing

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

def check_p(p):
    for r in [1, 2]:
        mod = p**(3*r)
        for n in range(1, 100):
            v1 = a(n * p**r)
            v2 = a(n * p**(r-1))
            if v1 % mod != v2 % mod:
                return f"Counterexample! p={p}, r={r}, n={n}"
    return None

if __name__ == '__main__':
    sys.set_int_max_str_digits(200000)
    primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    pool = multiprocessing.Pool(processes=multiprocessing.cpu_count())
    results = pool.map(check_p, primes)
    for res in results:
        if res:
            print(res)
    print("Massive check complete.")
