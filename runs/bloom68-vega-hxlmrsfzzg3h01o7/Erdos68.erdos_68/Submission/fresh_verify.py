#!/usr/bin/env python3
"""Exact checks of finite claims in the independent factorial-series attack.
No floating point and no numerical approximation to the infinite sum are used.
The universally quantified analytic claims are proved in FreshAttack.lean.
"""
from fractions import Fraction
from math import factorial, gcd, isqrt, lcm

p = 139
assert all(p % d for d in range(2, isqrt(p) + 1))
partial = Fraction(0)
L = 1
hits = []
for n in range(2, 138):
    a = factorial(n) - 1
    assert a > 0
    assert factorial(n + 1) - 1 == (n + 1) * a + n
    assert gcd(a, factorial(n + 1) - 1) == 1
    partial += Fraction(1, a)
    L = lcm(L, a)
    if n == 4:
        assert factorial(4) * partial == Fraction(3432, 115)
    if a % p == 0:
        assert a % (p * p) != 0
        hits.append((n, (a // p) % p))
    if n >= 5:
        assert Fraction(L, factorial(n + 1) - 1) > 1

assert hits == [(69, 6), (122, 49), (137, 73)]
assert sum(pow(u, -1, p) for _, u in hits) % p == 0
assert partial.denominator % p != 0
assert L == p * partial.denominator

# Check the finite geometric identity and its nonzero remainder exactly.
for n in range(2, 21):
    f = factorial(n)
    for K in range(9):
        truncated = sum((Fraction(1, f**j) for j in range(1, K + 1)), Fraction(0))
        remainder = Fraction(1, f**K * (f - 1))
        assert remainder > 0
        assert Fraction(1, f - 1) == truncated + remainder

# Validate the algebra behind the tail bounds at a finite range;
# FreshAttack.lean proves the statements for every index.
for N in range(3, 201):
    f = factorial(N)
    first = Fraction(f, factorial(N + 1) - 1)
    geometric_upper = first * Fraction(N + 2, N + 1)
    assert Fraction(1, N + 1) < first
    assert geometric_upper < Fraction(1, N)

print('All exact finite checks passed.')
print('139-divisible terms through 137 (index, quotient mod 139):', hits)
print('L_137 / reduced_denominator(P_137) =', L // partial.denominator)
print('No conclusion about irrationality is inferred from these finite computations.')
