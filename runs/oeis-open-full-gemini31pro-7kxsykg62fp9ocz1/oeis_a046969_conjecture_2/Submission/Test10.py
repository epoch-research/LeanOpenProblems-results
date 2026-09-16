from sage.all import bernoulli, factor

n = 17
B = bernoulli(2*n)
val = (B / (2*n*(2*n-1))).denominator()
print(f"n=17, val={val}, p={val//12}")
