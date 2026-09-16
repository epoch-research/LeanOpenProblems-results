from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

for n in range(2, 2000):
    an = a(n)
    if an % 12 != 0: continue
    if not is_prime(an // 12): continue
    an_minus_1 = a(n - 1)
    if an_minus_1 % 12 != 0: continue
    an_plus_2 = a(n + 2)
    if an_plus_2 % 12 != 0: continue
    
    c1 = ((an_minus_1 // 12) - (n - 1)) % 6 == 0
    c2 = ((an // 12) - n) % 6 == 0
    c3 = ((an_plus_2 // 12) - (n + 2)) % 6 == 0
    if not (c1 and c2 and c3):
        print(f"COUNTEREXAMPLE: n={n}")
        break
    else:
        print(f"Match: n={n}")
else:
    print("Done 2000")
