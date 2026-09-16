from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(2, 3000):
    an = a(n)
    if an % 12 != 0: continue
    p = an // 12
    if not is_prime(p): continue
    # Found a prime!
    # Check the conditions
    c1 = (a(n-1) % 12 == 0) and ((a(n-1)//12 - (n-1)) % 6 == 0)
    c2 = ((p - n) % 6 == 0)
    c3 = (a(n+2) % 12 == 0) and ((a(n+2)//12 - (n+2)) % 6 == 0)
    if not (c1 and c2 and c3):
        print(f"COUNTEREXAMPLE: n={n}")
        break
    else:
        print(f"MATCH: n={n}, p={p}")
else:
    print("NO COUNTEREXAMPLE UP TO 3000")
