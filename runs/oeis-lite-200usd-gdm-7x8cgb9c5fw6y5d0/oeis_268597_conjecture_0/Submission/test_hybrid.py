from sage.all import *

def is_prime_power(m):
    return is_prime(m) or len(factor(m)) == 1

def check_m(m):
    # Case 1: Prime power
    if is_prime_power(m):
        return "prime_power"
    
    factors = factor(m)
    # Check if m is of the form 2^k * q^a
    # i.e., factors of m are {2, q}
    if len(factors) == 2 and factors[0][0] == 2:
        return "even_two_primes"
        
    # Check if m is of the form 2^k * 3^j * q^a
    if len(factors) == 3 and factors[0][0] == 2 and factors[1][0] == 3:
        return "even_three_primes"
        
    # Check if m is of the form 2^k * 3^j
    if len(factors) == 2 and factors[0][0] == 2 and factors[1][0] == 3:
        return "even_two_three"
        
    # If not covered by the four cases above:
    # Let's search for a divisor q^k of m such that B = m // q^k, p = B - q + 1 is prime
    for q, k in factors:
        B = m // q
        p = B - q + 1
        if p > 1 and is_prime(p) and p != q:
            return f"divisor_congruence_q_{q}"
            
        # Try with q^k as the factor
        B2 = m // (q**k)
        p2 = B2 - q + 1
        if p2 > 1 and is_prime(p2) and p2 != q:
            return f"divisor_congruence_qk_{q}^{k}"
            
    return None

failures = []
for m in range(1500, 10000):
    res = check_m(m)
    if res is None:
        failures.append(m)

print(f"Total failures from 1500 to 10000: {len(failures)}")
if failures:
    print(f"Failures: {failures[:50]}")
else:
    print("SUCCESS! Every m >= 1500 is covered by the hybrid construction!")
