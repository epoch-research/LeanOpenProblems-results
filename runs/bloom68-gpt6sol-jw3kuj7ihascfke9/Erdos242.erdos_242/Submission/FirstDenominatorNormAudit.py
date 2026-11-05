#!/usr/bin/env python3
"""Finite, independent integer/rational audits for FirstDenominatorNorm.lean.

The complete Lean theorems cover the indicated *local* claims. These finite
calculations are NOT an all-prime Erdős--Straus proof. In particular, the
coordinate-multiple exclusion for p=66529 below is a Python-only finite check.
"""

from fractions import Fraction
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % r for r in range(2, isqrt(n) + 1))


def factor(n):
    assert n > 0
    result = {}
    r = 2
    while r * r <= n:
        while n % r == 0:
            result[r] = result.get(r, 0) + 1
            n //= r
        r += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def square_divisors(x):
    ds = [1]
    for r, power in factor(x).items():
        ds = [d * r**i for i in range(2 * power + 1) for d in ds]
    assert len(ds) == len(set(ds))
    return ds


def exact_types(p, x):
    assert p < 4 * x and 2 * x < p
    a = 4 * x - p
    ds = square_divisors(x)  # all c,d | x^2, not just divisors of x
    I = [c for c in ds if (4 * c + 1) % a == 0]
    II = [d for d in ds if 0 < d < x and (x + d) % a == 0]
    return I, II


def check_triple(p, x, y, z):
    assert 1 <= x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    return (x, y, z)


def type_i_triple(p, x, c):
    assert c in exact_types(p, x)[0]
    a = 4 * x - p
    d = x * x // c
    assert x * x == d * c and (p * x + d) % a == 0
    assert (p * x + p * p * c) % a == 0
    return check_triple(p, x, (p * x + d) // a, (p * x + p * p * c) // a)


def type_ii_triple(p, x, d):
    assert d in exact_types(p, x)[1]
    a = 4 * x - p
    b = x * x // d
    assert x * x == b * d and (x + b) % a == 0
    return check_triple(p, x, p * (x + d) // a, p * (x + b) // a)


# p, (u,v), first success j, exact branch/divisor and a dyadic exponent e.
CASES = (
    (193, 1, 4, 1, 'I', 5, 0),
    (2521, 22, 7, 5, 'II', 8, 2),
    (66529, 85, 56, 4, 'I', 2179447, 1),
    (18481, 17, 38, 4, 'II', 125, 0),
    (2473, 16, 11, 1, 'I', 5, 1),
    (409, 10, 1, 1, 'II', 1, 6),
)

for p, u, v, first_j, branch, divisor, exponent in CASES:
    q = (p + 3) // 4
    k = (p - 1) // 24
    assert prime(p) and p == 24 * k + 1 and q == 6 * k + 1
    assert q == u*u + 3*v*v and gcd(u, v) == 1 and v > 0
    assert all(prime(r) and r % 3 == 1 for r in factor(q))
    assert exact_types(p, q) == ([], [])
    for j in range(first_j):
        assert exact_types(p, q + j) == ([], []), (p, j)

    x = q + first_j
    assert divisor in (exact_types(p, x)[0] if branch == 'I' else exact_types(p, x)[1])
    triple = (type_i_triple(p, x, divisor) if branch == 'I'
              else type_ii_triple(p, x, divisor))

    t = 4*v*v - 1
    twin = 2**exponent * t
    assert t == (2*v-1)*(2*v+1)
    assert p == (2*u)**2 + 3*t
    assert q <= twin <= 2*q - 2
    assert exact_types(p, twin) == ([], [])
    # Quadratic signs of *all* prime factors of the bad candidate really are +1.
    assert all(pow(r, (p-1)//2, p) == 1 for r in factor(twin))
    print(f'p={p:<6} q={q:<6} (u,v)=({u},{v}) first j={first_j} '
          f'branch={branch} divisor={divisor} ordered={triple} '
          f'dyadic failed x={twin}')

# Correct Jacobi sign is not an exact divisor-residue match at a norm axis.
p, m = 2473, 11
h = 4*m-1
assert prime(h) and pow(p, (h-1)//2, h) == h-1
assert (-p*pow(4, -1, h)) % h == 16
assert [d for d in square_divisors(m) if d <= m*m] == [1, 11, 121]
assert all((p+4*d) % h for d in square_divisors(m))

p, u, v = 66529, 85, 56
assert (p+3)//4 == u*u + 3*v*v
for m in (u, v):
    h = 4*m - 1
    assert all((p+4*d) % h for d in square_divisors(m))
assert prime(223) and pow(p, 111, 223) == 222
assert (-p*pow(4, -1, 223)) % 223 == 37

# A stronger *finite* negative test: even allowing every eligible multiple
# of u or of v as the first denominator (not just the Type-II parameter m=u/v),
# no full Type-I/II square divisor works at this one, nevertheless soluble, p.
for coord in (u, v):
    low = (u*u + 3*v*v + coord - 1)//coord * coord
    xs = range(low, (p - 1)//2 + 1, coord)
    for x in xs:
        assert exact_types(p, x) == ([], []), (p, coord, x)
    print(f'p={p}, coordinate={coord}, checked {len(xs)} eligible multiples, '
          f'none with either complete certificate')

# Norm representation alone is weaker than the split-prime condition.
assert 25 == 5**2 + 3*0**2 and 5 in exact_types(97, 25)[0]
assert 5 in exact_types(97, 25)[1]
print('All six stress tests and the finite coordinate-multiple checks pass.')
