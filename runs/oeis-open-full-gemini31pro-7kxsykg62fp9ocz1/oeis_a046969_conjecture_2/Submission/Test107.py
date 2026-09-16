from sage.all import bernoulli, factor, divisors, is_prime
n = 49176
m = 2*n
# We just need to know if the denominator is a multiple of 12.
# Which means v_2(denom) >= 2 and v_3(denom) >= 1.
# denom = D_m * m * (m-1) / gcd(N_m, D_m * m * (m-1))
# Since gcd(N_m, D_m) = 1, denom = D_m * (m * (m-1)) / gcd(N_m, m * (m-1))
# D_m has 2 and 3. So v_2(D_m) = 1, v_3(D_m) = 1.
# m = 98352 = 16 * 6147. So v_2(m) = 4, v_3(m) = 1.
# m-1 is odd, not divisible by 3.
# We need v_2(N_m). By Adams, v_2(N_m) = 0? No, Adams doesn't apply to 2.
# By von Staudt-Clausen, v_2(B_m) = -1.
# So v_2(B_m / (m(m-1))) = v_2(B_m) - v_2(m) = -1 - 4 = -5.
# So v_2(denom) = 5.
# v_3(B_m) = -1.
# v_3(B_m / m) = -1 - 1 = -2.
# So v_3(denom) = 2.
# So denom is a multiple of 2^5 * 3^2 = 288.
# Which is a multiple of 12!
print("Yes!")
