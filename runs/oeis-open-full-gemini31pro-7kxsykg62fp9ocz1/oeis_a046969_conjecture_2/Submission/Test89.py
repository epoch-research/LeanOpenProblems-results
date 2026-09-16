from sage.all import bernoulli, factor
n = 7
m = 2*n
b = bernoulli(m)/m
print(f"n=7, m={m}")
print(f"b = {b}")
print(f"factor(m) = {factor(m)}")
