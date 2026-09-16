from sage.all import bernoulli, Mod
b20 = bernoulli(20) / 20
print(f"B_20 / 20 = {b20}")
num = b20.numerator()
den = b20.denominator()
val = Mod(num, 283) / Mod(den, 283)
print(f"B_20 / 20 mod 283 = {val}")
