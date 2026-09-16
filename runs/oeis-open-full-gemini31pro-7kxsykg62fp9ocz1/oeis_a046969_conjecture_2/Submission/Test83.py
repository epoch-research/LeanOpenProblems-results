from sage.all import bernoulli, factor
n = 2689
m = 2*n
print("Computing b...")
b = bernoulli(m) / (m*(m-1))
an = b.denominator()
print(f"a({n}) = {an}")
print(f"an % 12 = {an % 12}")
print(f"an / 12 = {an // 12}")
print(factor(an // 12))
