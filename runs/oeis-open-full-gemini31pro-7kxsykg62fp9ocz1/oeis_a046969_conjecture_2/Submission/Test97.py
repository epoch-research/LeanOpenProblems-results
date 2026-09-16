from sage.all import bernoulli, Mod
b = bernoulli(44) / 44
print(b.numerator() % 59)
print(Mod(b.numerator(), 59) / Mod(b.denominator(), 59))
