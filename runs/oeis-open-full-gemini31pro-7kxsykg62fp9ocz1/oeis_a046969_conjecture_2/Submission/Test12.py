from sage.all import bernoulli
B = bernoulli(12)
val = (B / (12*11)).denominator()
print(val, val//12)
