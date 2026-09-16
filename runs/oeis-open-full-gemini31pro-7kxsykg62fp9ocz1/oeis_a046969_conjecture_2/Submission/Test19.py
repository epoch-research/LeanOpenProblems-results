from sage.all import bernoulli
for n in range(1, 10):
    print((bernoulli(2*n) / (2*n*(2*n-1))).denominator(), end=", ")
print()
