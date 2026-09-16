def primes(n):
    b = [True] * n
    ps = []
    for p in range(2, n):
        if b[p]:
            ps.append(p)
            for i in range(p*p, n, p):
                b[i] = False
    return set(ps)

MAX = 6 * 100000 + 4
ps = primes(MAX)

def a(n):
    for p in range(2, 6*n+3):
        if p in ps and (p-2) in ps:
            if (6*n-p) in ps and (6*n+2-p) in ps:
                return p
    return 0

zeros = []
for n in range(10000, 100000):
    if a(n) == 0:
        zeros.append(n)
        print(f"Zero found: {n}")

print("Done. Zeros:", zeros)
