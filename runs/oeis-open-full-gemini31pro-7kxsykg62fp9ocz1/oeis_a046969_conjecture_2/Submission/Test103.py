from sage.all import bernoulli, factor
n = 49177
m = 2*n
# We want the denominator of B_m / (m(m-1)).
# Let D be the denominator of B_m
# B_m = N / D
# B_m / (m(m-1)) = N / (D * m * (m-1))
# The denominator of this fraction is D * m * (m-1) / gcd(N, D * m * (m-1))
# Since N and D are coprime (von Staudt-Clausen), gcd(N, D * m * (m-1)) = gcd(N, m * (m-1)).
# So the denominator is D * m * (m-1) / gcd(N, m * (m-1)).
print("gcd(N, m * (m-1)) must cancel m completely and leave exactly 1667 in m-1.")
