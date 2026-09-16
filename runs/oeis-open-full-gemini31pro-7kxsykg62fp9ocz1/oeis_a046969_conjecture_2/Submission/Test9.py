from sage.all import bernoulli, factor

for n in range(1, 20):
    B = bernoulli(2*n)
    den1 = (B / (2*n)).denominator()
    print(f"n={n}, 2n={2*n}, den={factor(den1)}")
