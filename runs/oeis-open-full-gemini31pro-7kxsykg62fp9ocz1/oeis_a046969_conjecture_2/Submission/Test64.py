from sage.all import bernoulli
def a(n):
    m = 2*n
    return (bernoulli(m) / (m*(m-1))).denominator()

print(f"a(18)/12 mod 6 = {(a(18)//12)%6}")
