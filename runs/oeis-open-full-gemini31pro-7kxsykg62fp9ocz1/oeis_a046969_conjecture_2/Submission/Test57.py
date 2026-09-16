from sage.all import bernoulli
for n in range(7, 1000, 6):
    m = 2*n
    r = 2*n - 1
    # Check if r divides numerator of B_m / m
    b = bernoulli(m) / m
    if b.numerator() % r == 0:
        print(f"WOW! n={n} completely cancelled!")
