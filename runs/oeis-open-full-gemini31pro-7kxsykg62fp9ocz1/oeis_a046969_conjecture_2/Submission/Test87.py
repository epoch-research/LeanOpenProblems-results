from sage.all import is_prime, factor, bernoulli

n = 49177
m = 2*n
print("m =", m)
print("factor(m) =", factor(m))
print("factor(m-1) =", factor(m-1))
# We check if 59 | N_m
b44 = bernoulli(44) / 44
print("b44.numerator() % 59 ==", b44.numerator() % 59)
# By Kummer, since m = 98354 = 44 mod 58, and 59 is regular? No, 59 is irregular!
# Wait, 59 is an irregular prime (divides numerator of B_44).
# This is exactly why 59 | N_m !
# So 59 is cancelled.
# What about 1667?
b74 = bernoulli(74) / 74
print("b74.numerator() % 1667 ==", b74.numerator() % 1667)
