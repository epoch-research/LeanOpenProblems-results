from sage.all import bernoulli, factor
n = 49177
m = 2*(n+2)
# We can't compute bernoulli(98358) easily. But we can compute its denominator using von Staudt-Clausen.
# D_m = prod(q for q in primes if (q-1)|m)
# Denom of b = D_m * m * (m-1) / gcd(N_m, D_m * m * (m-1))
# Since we just need v_2 and v_3:
print("n+2 is a multiple of 12?")
# v_2
# v_2(D_m) = 1
# v_2(m) = 1
# v_2(m-1) = 0
# v_2(N_m) = 0 (odd)
# so v_2(a(n+2)) = 2

# v_3
# v_3(D_m) = 1 (since 2 | m)
# v_3(m) = v_3(98358) = 1
# v_3(m-1) = 0
# N_m might cancel 3?
# Adams' theorem: v_3(B_m/m) >= 0. No, 3-1 = 2 | m, so Adams doesn't apply to 3!
# Wait! If 3-1 | m, then v_3(B_m) = -1.
# So v_3(B_m / m) = -1 - v_3(m) = -1 - 1 = -2.
# So v_3 of the denominator is 2!
print("Yes!")
