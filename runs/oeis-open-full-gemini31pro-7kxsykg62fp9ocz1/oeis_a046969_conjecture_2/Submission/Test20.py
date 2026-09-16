from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

print("n=31")
an = a(31)
print("a(31) % 12 ==", an % 12)
print("prime?", is_prime(an // 12))
print("a(30) % 12 ==", a(30) % 12)
print("a(33) % 12 ==", a(33) % 12)
