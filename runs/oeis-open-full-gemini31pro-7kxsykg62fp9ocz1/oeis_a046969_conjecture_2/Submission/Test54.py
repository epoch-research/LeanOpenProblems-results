from sage.all import bernoulli, factor
n = 55
m = 2*n
an = (bernoulli(m) / (m * (m-1))).denominator()
print(f"n=55, an/12 = {an/12}")
print(factor(an // 12))
