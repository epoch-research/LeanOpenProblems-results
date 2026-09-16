from sage.all import bernoulli, factor
m = 1148
b = bernoulli(m) / m
num = b.numerator()
print(f"num % 37 = {num % 37}")
