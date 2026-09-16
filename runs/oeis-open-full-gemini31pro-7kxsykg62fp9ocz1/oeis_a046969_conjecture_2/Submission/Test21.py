from sage.all import bernoulli

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

print("a(30)/12 =", a(30) // 12)
print("mod 6 =", (a(30) // 12) % 6)
