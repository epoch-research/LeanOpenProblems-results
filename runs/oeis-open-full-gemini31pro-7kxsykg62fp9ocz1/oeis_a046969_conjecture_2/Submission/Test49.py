from sage.all import bernoulli, factor, Mod
num = bernoulli(5378).numerator()
print(f"num % 2689 = {num % 2689}")
print(f"num % 283 = {num % 283}")
