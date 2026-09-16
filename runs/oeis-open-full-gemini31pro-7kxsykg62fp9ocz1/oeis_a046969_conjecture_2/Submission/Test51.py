from sage.all import bernoulli
for n in range(4, 100, 6):
    m = 2*n
    k = m * (m-1)
    an = (bernoulli(m) / k).denominator()
    print(f"n={n}, an={an}, p={an/12}")
