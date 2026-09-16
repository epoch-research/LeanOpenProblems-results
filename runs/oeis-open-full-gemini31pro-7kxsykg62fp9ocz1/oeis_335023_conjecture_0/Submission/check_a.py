import math

def check():
    F = 0
    fact = 1
    g_prev = 1
    for k in range(1, 2000):
        sign = 1 if k % 2 == 0 else -1
        F = k * F + sign * fact
        fact *= k
        g = math.gcd(fact, F)
        if k > 1:
            a = g / g_prev
            if a == 1:
                if not is_prime(k):
                    print(f"Counterexample: n = {k-1}, n+1 = {k}")
        g_prev = g

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

check()
