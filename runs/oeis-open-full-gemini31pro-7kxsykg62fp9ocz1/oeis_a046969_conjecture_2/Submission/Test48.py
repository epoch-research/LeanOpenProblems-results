from sage.all import bernoulli, is_prime

def a(n):
    if n == 0: return 0
    m = 2 * n
    k = m * (m - 1)
    return (bernoulli(m) / k).denominator()

n = 2689
an = a(n)
print(f"n={n}")
print(f"an % 12 = {an % 12}")
p = an // 12
print(f"p = {p}, is_prime={is_prime(p)}")
an_minus_1 = a(n-1)
print(f"a(n-1) % 12 = {an_minus_1 % 12}")
an_plus_2 = a(n+2)
print(f"a(n+2) % 12 = {an_plus_2 % 12}")
print(f"an/12 - n mod 6 = {(p - n) % 6}")
print(f"a(n-1)/12 - (n-1) mod 6 = {(an_minus_1//12 - (n-1)) % 6}")
print(f"a(n+2)/12 - (n+2) mod 6 = {(an_plus_2//12 - (n+2)) % 6}")
