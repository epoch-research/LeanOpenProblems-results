from sage.all import is_prime, factor, primes

# We want to find n = 1 mod 6 such that a(n)/12 is prime and NOT 1 mod 6.
# If a(n)/12 is prime, it means the denominator of B_2n / (2n(2n-1)) has exactly one prime > 3.
# D_2n has primes q where q-1 | 2n.
# Since 2n = 12k+2, q-1 | 12k+2.
# So q can only be 3, 2, or some primes = 5 mod 12.
# Wait! If q-1 | 12k+2, then q = 5 mod 12 is POSSIBLE!
# Example: 12k+2 = 4. q-1 = 4 => q=5.
# But for n=1 mod 6, 2n = 12k+2.
# Can 4 divide 12k+2? No! 12k+2 is 2 mod 4. So 4 NEVER divides 2n!
# So q-1 cannot be a multiple of 4.
# Thus q cannot be 1 mod 4.
# Can q-1 be a multiple of 3? 12k+2 is 2 mod 3. So 3 NEVER divides 2n.
# So q cannot be 1 mod 3.
# This means q-1 is only divisible by primes > 3 and by 2 (exactly once).
# Thus q-1 = 2 * r_1 * r_2 ...
# So q = 2 * r + 1.
# What if 2n = 12k+2 has a divisor d = q-1?
pass
