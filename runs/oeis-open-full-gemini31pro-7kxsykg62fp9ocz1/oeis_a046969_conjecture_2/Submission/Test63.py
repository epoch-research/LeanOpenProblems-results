from sage.all import bernoulli, gcd
for n in range(1, 100):
    m = 2*n
    num = bernoulli(m).numerator()
    g = gcd(num, m - 1)
    if g > 1:
        print(f"n={n}, 2n-1={m-1}, gcd={g}")
