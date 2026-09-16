from sage.all import bernoulli
for n in [4, 34, 76, 94]:
    m = 2*n
    b = bernoulli(m) / (m * (m-1))
    an = b.denominator()
    print(f"n={n}, an={an}, p={an/12}")
