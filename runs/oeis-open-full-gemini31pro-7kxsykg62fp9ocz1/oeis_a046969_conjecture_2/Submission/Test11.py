from sage.all import bernoulli

def a(n):
    if n == 0: return 1
    B = bernoulli(2*n)
    return (B / (2*n*(2*n-1))).denominator()

print(a(5))
