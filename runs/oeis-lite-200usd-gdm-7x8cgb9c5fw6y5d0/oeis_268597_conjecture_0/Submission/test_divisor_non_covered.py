from sage.all import *

def check_m(m):
    factors = factor(m)
    # Case 1: Prime power
    if len(factors) == 1:
        return "prime_power"
    # Case 2: 2^k * q^a
    if len(factors) == 2 and factors[0][0] == 2:
        return "even_two_primes"
    # Case 3: 2^k * 3^j * q^a
    if len(factors) == 3 and factors[0][0] == 2 and factors[1][0] == 3:
        return "even_three_primes"
    # Case 4: 2^k * 3^j
    if len(factors) == 2 and factors[0][0] == 2 and factors[1][0] == 3:
        return "even_two_three"
        
    # If not covered by Cases 1-4, let's search for the divisor-prime witness:
    n = m - 1
    target = 2 * m
    divs = divisors(target)
    for A in divs:
        rhs = m - A
        if rhs == 0:
            if A % euler_phi(A) == 0:
                p = 2
                while True:
                    if is_prime(p) and gcd(p, A) == 1:
                        x = A * p
                        if euler_phi(x) > n:
                            return f"A={A}, p={p} (rhs=0)"
                    p += 1
        else:
            for d in divisors(abs(rhs)):
                p = d + 1
                if is_prime(p) and gcd(p, A) == 1:
                    x = A * p
                    ph = euler_phi(x)
                    if ph > n and (x - 1) % ph == n:
                        return f"A={A}, p={p} (rhs={rhs}, d={d})"
    return "FAILED"

failures = []
for m in range(2, 5000):
    res = check_m(m)
    if res == "FAILED":
        failures.append(m)

print(f"Failures: {failures}")
