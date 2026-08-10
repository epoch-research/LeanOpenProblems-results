import math

def is_prime(n):
    if n < 2:
        return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

# Compute n! modulo M (as a list of factorials)
def get_factorials(n, M):
    facts = [1] * (n + 1)
    for i in range(1, n + 1):
        facts[i] = (facts[i - 1] * i) % M
    return facts

# Compute modular inverse
def mod_inverse(a, M):
    try:
        return pow(a, -1, M)
    except ValueError:
        # If not coprime, we can't use simple modular inverse.
        # But for our choose, we can do it by keeping track of p-factors,
        # or since p^3 is small, we can just do it.
        return None

# To compute choose(n, k) modulo p^3, we can use the fact that
# choose(n, k) = n! / (k! * (n-k)!)
# Since we need choose(n, k) modulo p^3, and p is prime,
# we can write each number x as p^v * u, where gcd(u, p) = 1.
def get_p_val_and_coprime(x, p):
    v = 0
    while x > 0 and x % p == 0:
        v += 1
        x //= p
    return v, x

def choose_mod(n, k, p, p3):
    if k < 0 or k > n:
        return 0
    if k == 0 or k == n:
        return 1
    # We can compute choose(n, k) by computing the product of (n - i) / (i + 1)
    # keeping track of the power of p.
    num_p = 0
    num_coprime = 1
    den_p = 0
    den_coprime = 1
    for i in range(k):
        v_num, u_num = get_p_val_and_coprime(n - i, p)
        num_p += v_num
        num_coprime = (num_coprime * u_num) % p3
        
        v_den, u_den = get_p_val_and_coprime(i + 1, p)
        den_p += v_den
        den_coprime = (den_coprime * u_den) % p3
    
    p_pow = num_p - den_p
    if p_pow >= 3:
        return 0
    inv_den = pow(den_coprime, -1, p3)
    val = (num_coprime * inv_den) % p3
    val = (val * (p ** p_pow)) % p3
    return val

def a_mod(n, p, p3):
    total = 0
    for k in range(n + 1):
        c1 = choose_mod(n, k, p, p3)
        c2 = choose_mod(n + k, k, p, p3)
        c3 = choose_mod(3 * n + 2 * k, n, p, p3)
        term = (c1 * c1) % p3
        term = (term * c2) % p3
        term = (term * c3) % p3
        total = (total + term) % p3
    return total

def test():
    print("Searching for counterexample...")
    for p in range(5, 1000):
        if is_prime(p):
            p3 = p ** 3
            lower_bound = (2 * p + 3) // 3
            upper_bound = p - 1
            for n in range(lower_bound, upper_bound + 1):
                val = a_mod(n, p, p3)
                if val != 0:
                    print(f"COUNTEREXAMPLE FOUND: p = {p}, n = {n}")
                    print(f"a(n) % p^3 = {val}")
                    return
            if p % 50 == 3 or p % 50 == 1 or p % 50 == 7 or p % 50 == 9: # just some status updates
                print(f"Checked up to p = {p}")
    print("Checked all primes up to 1000. No counterexamples.")

if __name__ == "__main__":
    test()
