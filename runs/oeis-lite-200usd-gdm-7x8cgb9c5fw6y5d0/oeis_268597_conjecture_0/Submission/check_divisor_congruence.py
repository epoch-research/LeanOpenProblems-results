import sympy

def check_m(m):
    if sympy.isprime(m):
        return "PRIME"
    n = m - 1
    # We want to find a divisor A of 2*m and a prime p such that:
    # x = A * p
    # phi(x) > n and (x - 1) % phi(x) == n
    target = 2 * m
    # Divisors of 2*m
    divs = []
    for d in range(1, int(target**0.5) + 1):
        if target % d == 0:
            divs.append(d)
            if d*d != target:
                divs.append(target // d)
    divs.sort()
    
    for A in divs:
        rhs = m - A
        if rhs == 0:
            # We want x = A * p
            # If gcd(p, A) == 1, phi(x) = phi(A) * (p-1)
            # x - m = A*p - A = A*(p-1). We want this to be a multiple of phi(x) = phi(A)*(p-1)
            # which is A*(p-1) = k * phi(A)*(p-1) <=> A = k * phi(A).
            if A % sympy.totient(A) == 0:
                # Find a prime p coprime to A
                p = 2
                while True:
                    if sympy.isprime(p) and sympy.gcd(p, A) == 1:
                        x = A * p
                        if sympy.totient(x) > n:
                            return f"A={A}, p={p} (rhs=0)"
                        break
                    p += 1
        else:
            # We want x = A * p. If gcd(p, A) == 1,
            # x - m = A*p - m. We want A*p - m = k * phi(A)*(p-1)
            # <=> A*p - m = k * phi(A)*p - k * phi(A)
            # <=> (A - k * phi(A)) * p = m - k * phi(A).
            # Let's test various values of k (positive or negative)
            for k in [1, 2, 3, 4, 5, -1, -2, -3]:
                denom = A - k * sympy.totient(A)
                if denom != 0:
                    num = m - k * sympy.totient(A)
                    if num % denom == 0:
                        p = num // denom
                        if p > 1 and sympy.isprime(p) and sympy.gcd(p, A) == 1:
                            x = A * p
                            ph = sympy.totient(x)
                            if ph > n and (x - 1) % ph == n:
                                return f"A={A}, p={p}, k={k}"
    return "FAILED"

failed = []
for m in range(501, 2000):
    if not sympy.isprime(m):
        res = check_m(m)
        if res == "FAILED":
            failed.append(m)

print(f"Failed count: {len(failed)}")
if failed:
    print(f"Failed: {failed[:50]}")
else:
    print("SUCCESS for all composite m from 501 to 2000!")
