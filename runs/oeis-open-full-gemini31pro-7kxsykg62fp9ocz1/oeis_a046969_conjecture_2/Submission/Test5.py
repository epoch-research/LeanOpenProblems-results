def bernoulli(n):
    from fractions import Fraction
    A = [0] * (n + 1)
    for m in range(n + 1):
        A[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            A[j - 1] = j * (A[j - 1] - A[j])
    return A[0]

def a(n):
    if n == 0: return 1
    B = bernoulli(2 * n)
    d = 2 * n * (2 * n - 1)
    val = B / d
    return val.denominator

print("n=19:", a(19))
print("n=31:", a(31))
