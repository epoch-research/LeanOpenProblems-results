from sage.all import is_prime, divisors, bernoulli

for n in [25, 85, 121, 187, 235, 295, 355, 391, 493, 505]:
    m = 2*n
    k = m * (m - 1)
    val = (bernoulli(m) / k).denominator() // 12
    print(f"n={n}, a(n)/12 = {val}, is_prime={is_prime(val)}")
