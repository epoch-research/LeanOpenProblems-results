import sympy

def phi(n):
    return sympy.totient(n)

# We want to find k >= 2 such that phi(m * k) divides m * (k - 1)
# And we also need phi(m * k) > m - 1 (which is usually true since phi(m*k) >= phi(m*2))

failures = []
for m in range(4, 500):
    if not sympy.isprime(m):
        found = False
        for k in range(2, 10000):
            ph = phi(m * k)
            if ph > m - 1 and (m * (k - 1)) % ph == 0:
                # print(f"m={m:3d}, k={k:4d}, x={m*k:5d}, phi(x)={ph:5d}")
                found = True
                break
        if not found:
            failures.append(m)

print(f"Failures: {failures}")
