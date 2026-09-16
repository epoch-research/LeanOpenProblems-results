from sage.all import bernoulli
m = 18
b = bernoulli(m) / (m*(m-1))
an = b.denominator()
print(f"a(9)={an}, an%12 = {an%12}, an/12 = {an/12}")
