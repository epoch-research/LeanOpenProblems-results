from sage.all import bernoulli, factor
n = 17
m = 2*n
an = (bernoulli(m) / (m * (m-1))).denominator()
print(f"n=17, an={an}, p={an/12}")
print(f"factor(p) = {factor(an // 12)}")
