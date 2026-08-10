import math

limit = 2000005
covered = [False] * limit

# Rule 1, 2, 3
for n in range(9, limit):
    if n % 3 == 0 or n % 10 == 0:
        covered[n] = True

# We'll define a helper to apply coprime partition rule for prime p, partition (a, b)
# which works if n = p * m and gcd(a * b, m) == 1
def apply_rule(p, a, b):
    ab = a * b
    for n in range(p * ((9 + p - 1) // p), limit, p):
        if not covered[n]:
            m = n // p
            if math.gcd(ab, m) == 1:
                covered[n] = True

# Let's apply rules for several primes and their partitions:
# Prime partitions:
# p = 7 : a=2, b=5 (ab = 10)
apply_rule(7, 2, 5)
# p = 11 : a=1, b=10 (ab = 10)
apply_rule(11, 1, 10)
# p = 13 : a=1, b=12 (ab = 12)
apply_rule(13, 1, 12)
# p = 17 : a=5, b=12 (ab = 60)
apply_rule(17, 5, 12)
# p = 19 : a=4, b=15 (ab = 60)
apply_rule(19, 4, 15)
# p = 23 : a=3, b=20 (ab = 60)
apply_rule(23, 3, 20)
# p = 29 : a=12, b=17 (ab = 204)
apply_rule(29, 12, 17)
# p = 31 : a=4, b=27 (ab = 108)
apply_rule(31, 4, 27)
# p = 37 : a=5, b=32 (ab = 160)
apply_rule(37, 5, 32)
# p = 41 : a=1, b=40 (ab = 40)
apply_rule(41, 1, 40)
# p = 43 : a=16, b=27 (ab = 432)
apply_rule(43, 16, 27)
# p = 47 : a=20, b=27 (ab = 540)
apply_rule(47, 20, 27)

uncovered = sum(1 for n in range(9, 2000000 + 1) if not covered[n])
print(f"Total uncovered after applying these rules: {uncovered}")
