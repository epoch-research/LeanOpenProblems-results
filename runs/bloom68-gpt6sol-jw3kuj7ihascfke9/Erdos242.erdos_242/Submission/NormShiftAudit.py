#!/usr/bin/env python3
"""Independent integer/rational audit of NormShiftDescent (no external packages).

Finite searches here are checks of named examples, NOT an all-prime proof.
"""

from fractions import Fraction
from math import gcd, isqrt


def prime(n):
    return n >= 2 and all(n % q for q in range(2, isqrt(n) + 1))


def factors(n):
    assert n >= 1
    out = {}
    q = 2
    while q * q <= n:
        if n % q == 0:
            e = 0
            while n % q == 0:
                n //= q
                e += 1
            out[q] = e
        q += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def squared_divisors(n):
    ds = [1]
    for q, e in factors(n).items():
        old = list(ds)
        ds = [d * q**i for d in old for i in range(2 * e + 1)]
    return ds


def types(p, x):
    a = 4 * x - p
    assert p < 4 * x < 2 * p
    ds = squared_divisors(x)
    ci = [c for c in ds if (4 * c + 1) % a == 0]
    di = [d for d in ds if d < x and (x + d) % a == 0]
    return sorted(ci), sorted(di)


def check_triple(p, x, y, z):
    assert 0 < x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)


def type_i_triple(p, x, c):
    a = 4 * x - p
    assert c in squared_divisors(x) and (4 * c + 1) % a == 0
    r = x * x // c
    assert (p * x + r) % a == 0 and (p * x + p * p * c) % a == 0
    y = (p * x + r) // a
    z = (p * x + p * p * c) // a
    check_triple(p, x, y, z)
    return x, y, z


def type_ii_triple(p, x, d):
    a = 4 * x - p
    assert 0 < d < x and d in squared_divisors(x) and (x + d) % a == 0
    b = x * x // d
    assert (x + b) % a == 0
    y = p * (x + d) // a
    z = p * (x + b) // a
    check_triple(p, x, y, z)
    return x, y, z


# The supplied three examples, and a further split-norm prime that needs 26 shifts.
CASES = [
    # p, first successful j, primitive A, B, full Type-I cofactor, Type-II divisor
    (193, 1, 1, 4, 5, 20),
    (2521, 5, 22, 7, 477, 8),
    (66529, 4, 85, 56, 2179447, None),
    (8803369, 26, 1480, 59, None, 121),
]
for p, first_j, A, B, c, d in CASES:
    x0 = (p + 3) // 4
    assert prime(p) and p % 24 == 1
    assert x0 == A * A + 3 * B * B and gcd(A, B) == 1 and x0 % 2 == 1
    assert all(r % 3 == 1 for r in factors(x0))
    for j in range(first_j):
        assert types(p, x0 + j) == ([], []), (p, j)
    x = x0 + first_j
    I, II = types(p, x)
    assert c in I if c is not None else not I
    assert d in II if d is not None else not II
    witness = (type_ii_triple(p, x, d) if p in (2521, 8803369)
               else type_i_triple(p, x, c))
    print("p=", p, "x0=", x0, "first j=", first_j,
          "x=", x, "a=", 4 * first_j + 3,
          "full I/II=", bool(I), bool(II), "ordered=", witness)
assert prime(2200843)  # first denominator obstruction for 8803369 is prime.

# A norm is not sufficient to certify first-fiber failure: 25 is a norm but
# 5 (2 mod 3) is an inert factor, and both full types hold at x0=25.
assert prime(97) and 25 == 5**2 + 3 * 0**2
assert (5 in types(97, 25)[0]) and (5 in types(97, 25)[1])

# Norm-preserving coordinate move B=7 -> 9 for 2521: odd primitive norm,
# eligible x=22²+3·9²=727, a=387, and still no divisor certificate.
assert 727 == 22**2 + 3 * 9**2 and gcd(22, 9) == 1
assert types(2521, 727) == ([], [])

# Even an external nonresidue at a shifted x need not hit either exact
# divisor target: 135 divisors of 16644² miss both classes modulo 47.
p, x = 66529, 16644
assert x == (p + 3) // 4 + 11 and factors(x) == {2: 2, 3: 1, 19: 1, 73: 1}
assert pow(19, (p - 1) // 2, p) == p - 1
assert types(p, x) == ([], [])
assert len(squared_divisors(x)) == 135
assert {d % 47 for d in squared_divisors(x)} == set(range(1, 47)) - {35, 41, 44}
assert (-pow(4, -1, 47)) % 47 == 35 and (-x) % 47 == 41

# All identities of the three infinite norm-parameter families are checked
# for a sample of parameters; the algebraic Lean theorems cover every s.
for s in range(30):
    t = 5 * s + 2
    N = 1 + 3 * (2 * t)**2
    q = 10 + 48 * s + 60 * s**2
    p = 4 * N - 3
    x = N + 1
    assert x == 5 * q and p == 20 * q - 7 and gcd(1, 2 * t) == 1
    assert x % 5 == 0 and (4 * 5 + 1) % 7 == 0
    check_triple(p, x, 5 * q * (3 * q - 1), 5 * p * (3 * q - 1))

    A = 22 + 1932 * s
    B = 7
    N = A * A + 3 * B * B
    w = 2 + 308 * s + 13524 * s**2
    h = 3 * w + 1
    u = 23 * w + 7
    p = 4 * N - 3
    x = N + 5
    c = 9 * u
    d = 8
    assert gcd(A, B) == 1 and N % 2 == 1 and p % 24 == 1
    assert p == 1104 * w + 313 and x == 12 * u and 4 * x - p == 23
    assert c > 0 and x * x % c == 0 and x % c != 0 and (4 * c + 1) % 23 == 0
    assert 0 < d < x and x * x % d == 0 and x % d != 0 and (x + d) % 23 == 0
    check_triple(p, x, 4 * h * p, 6 * h * u * p)
    type_i_triple(p, x, c)

    A = 85 + 405384 * s
    B = 56
    N = A * A + 3 * B * B
    t = 6 + 28560 * s + 68104512 * s**2
    q = 19 * t + 17
    p = 4 * N - 3
    x = N + 4
    c = 127 * q * q
    assert gcd(A, B) == 1 and N % 2 == 1 and p % 24 == 1
    assert N + 4 == 127 * q and p == 508 * q - 19 and 4 * x - p == 19
    assert c > x and x * x % c == 0 and (4 * c + 1) % 19 == 0
    assert (p * q + 1) % 19 == 0
    check_triple(p, x, 127 * (p * q + 1) // 19,
                 p * q * (127 * (p * q + 1) // 19))
print("All norm-family polynomial identities also pass s=0,...,29.")
