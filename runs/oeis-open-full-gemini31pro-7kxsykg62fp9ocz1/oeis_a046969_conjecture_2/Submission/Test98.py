from sage.all import bernoulli, Mod
b = bernoulli(74) / 74
print(b.numerator() % 1667)
print(Mod(b.numerator(), 1667) / Mod(b.denominator(), 1667))
