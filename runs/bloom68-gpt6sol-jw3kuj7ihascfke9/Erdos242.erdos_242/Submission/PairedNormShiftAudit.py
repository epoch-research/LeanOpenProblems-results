#!/usr/bin/env python3
"""Exact finite audit of a specific Gaussian/48B-norm shift candidate set.

This script checks named prime inputs, *not* a universal Erdős--Straus claim.
All primality tests are deterministic trial division up to integer square root;
no external packages or probabilistic primality tests are used.
"""

from fractions import Fraction
from math import isqrt


def prime(n):
    return n >= 2 and all(n % r for r in range(2, isqrt(n) + 1))


def factors(n):
    assert n >= 1
    result = {}
    r = 2
    while r * r <= n:
        if n % r == 0:
            e = 0
            while n % r == 0:
                n //= r
                e += 1
            result[r] = e
        r += 1
    if n > 1:
        result[n] = 1
    assert all(prime(r) for r in result)
    return result


def square_divisors(x):
    result = [1]
    for r, e in factors(x).items():
        result = [d * r**i for d in result for i in range(2 * e + 1)]
    assert len(result) == len(set(result))
    return sorted(result)


def types(p, x):
    assert p < 4 * x and 2 * x < p
    a = 4 * x - p
    ds = square_divisors(x)
    return ([c for c in ds if (4 * c + 1) % a == 0],
            [d for d in ds if d < x and (x + d) % a == 0])


def gaussian(n):
    """All positive a<=b with a^2+b^2=n (up to sign and order)."""
    ans = []
    for a in range(1, isqrt(n // 2) + 1):
        b = isqrt(n - a * a)
        if b * b == n - a * a:
            ans.append((a, b))
    return ans


def norm48(n):
    """All positive A,B with A^2+48B^2=n."""
    ans = []
    for B in range(1, isqrt((n - 1) // 48) + 1):
        A = isqrt(n - 48 * B * B)
        if A * A + 48 * B * B == n and A > 0:
            ans.append((A, B))
    return ans


def triple(p, x, branch, w):
    I, II = types(p, x)
    a = 4 * x - p
    if branch == 'I':
        assert w in I
        c = w
        r = x * x // c
        assert (p * x + r) % a == (p * x + p * p * c) % a == 0
        y = (p * x + r) // a
        z = (p * x + p * p * c) // a
    else:
        assert branch == 'II' and w in II
        d = w
        b = x * x // d
        assert (x + d) % a == (x + b) % a == 0
        y = p * ((x + d) // a)
        z = p * ((x + b) // a)
    assert 0 < x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    return x, y, z


# These five primes include all four requested stress inputs and an additional
# even-B counterexample where BOTH complete types fail at the proposed shift.
cases = {
    # p: Gaussian coordinates of p, (A,B), B-shift x, success of B cofactor,
    #      success of each full type at that x
    193: ((7, 12), (1, 2), 50, True, True, True),
    2521: ((35, 36), (13, 7), 637, False, False, False),
    66529: ((55, 252), (239, 14), 16646, True, True, True),
    8803369: ((1360, 2637), (2251, 279), 2201121, False, False, False),
    3361: ((15, 56), (17, 8), 848, False, False, False),
}
shifted_factors = {
    193: ({2: 1, 97: 1}, {197: 1}),
    2521: ({2: 1, 13: 1, 97: 1}, {5: 2, 101: 1}),
    66529: ({2: 1, 5: 1, 6653: 1}, {66533: 1}),
    8803369: ({2: 1, 5: 1, 880337: 1}, {37: 1, 237929: 1}),
    3361: ({2: 1, 41: 2}, {5: 1, 673: 1}),
}
for p, (g, (A, B), x, cofactor_works, typeI, typeII) in cases.items():
    assert prime(p) and p % 24 == 1
    assert gaussian(p) == [g] and norm48(p) == [(A, B)]
    assert factors(p + 1) == shifted_factors[p][0]
    assert factors(p + 4) == shifted_factors[p][1]
    assert all(q == 2 or q % 4 == 1
               for s in (1, 4) for q in factors(p + s))
    assert gaussian(p + 1) and gaussian(p + 4)
    t, c = 4 * B - 1, 3 * B - 1
    assert x == (p + t) // 4 and 4 * x - p == t
    assert 4 * c + 1 == 3 * t and 12 * x == 3 * A * A + 17 + c * (48 * B + 20)
    assert p < 4 * x and 2 * x < p
    assert (x * x % c == 0) == cofactor_works
    I, II = types(p, x)
    assert (bool(I), bool(II)) == (typeI, typeII)
    assert (c in I) == cofactor_works
    if B % 2:
        assert x % 2 == 1 and c % 2 == 0
    else:
        assert (x * x % c == 0) == ((3 * A * A + 17)**2 % c == 0)
    print('48B shift:', p, 'B=', B, 't=', t, 'x=', x, 'c=', c,
          'c|x^2=', cofactor_works, 'full types=', bool(I), bool(II))

# Enumerate *all* representations of p,p+1,p+4, not just a selected
# representation of either composite norm. Every eligible coordinate
# product misses both full types for all five inputs. For 2521, 8803369
# and 3361 the extra 48B candidate also misses both types.
expected_products = {
    193: {84, 65},
    2521: {1260, 1189, 1118, 1258},
    66529: {23183, 29393},
    8803369: {3586320, 4401523, 2277826},
    3361: {1519, 1598},
}
for p, products in expected_products.items():
    actual = {a * b for s in (0, 1, 4) for a, b in gaussian(p + s)
              if p < 4 * a * b and 2 * a * b < p}
    assert actual == products
    assert all(types(p, x) == ([], []) for x in products)
    print('eligible Gaussian coordinate products, both types fail:', p,
          sorted(products))

# A precise finite set: products of coordinates in *all* Gaussian norms of
# p,p+1,p+4, together with the 48B shift, retaining only ordered candidates.
p = 3361
assert gaussian(p) == [(15, 56)]
assert gaussian(p + 1) == [(31, 49), (41, 41)]
assert gaussian(p + 4) == [(1, 58), (34, 47)]
candidates = {a * b for s in (0, 1, 4) for a, b in gaussian(p + s)
              if p < 4 * a * b and 2 * a * b < p}
candidates.add(848)
assert candidates == {848, 1519, 1598}
assert all(types(p, x) == ([], []) for x in candidates)

# Compact modular certificates for failure of both complete alternatives.
assert factors(848) == {2: 4, 53: 1}
res31 = {(2**i * 53**j) % 31 for i in range(9) for j in range(3)}
assert res31 == {1, 2, 4, 8, 16, 22, 13, 26, 21, 11, 19, 7, 14, 28, 25}
assert (-pow(4, -1, 31)) % 31 == 23 not in res31
assert -848 % 31 == 20 not in res31
assert 848**2 % 23 == 9

assert factors(1519) == {7: 2, 31: 1}
assert (4 * 1519 - p) % 3 == 0 and 1519 % 3 == 1
assert all(d % 3 == 1 for d in square_divisors(1519))

assert factors(1598) == {2: 1, 17: 1, 47: 1}
assert 4 * 1598 - p == 7 * 433
hits_mod7 = sorted(d for d in square_divisors(1598) if d % 7 == 5)
assert hits_mod7 == [47, 68, 37553, 54332]
assert [(4 * d + 1) % 433 for d in hits_mod7] == [189, 273, 395, 396]
assert [(1598 + d) % 433 for d in hits_mod7 if d < 1598] == [346, 367]

# For B=7, both full types at x=637 fail already modulo 3.
assert factors(637) == {7: 2, 13: 1}
assert (4 * 637 - 2521) % 3 == 0 and 637 % 3 == 1
assert all(d % 3 == 1 for d in square_divisors(637))

# For B=279, reduction modulo the prime 223 rules out *every* divisor,
# including the unrestricted version of Type II with d >= x.
p, x = 8803369, 2201121
assert prime(6271) and prime(223)
assert factors(x) == {3: 3, 13: 1, 6271: 1}
assert 4 * x - p == 5 * 223 and 6271 % 223 == 27 == 3**3
powers3 = {pow(3, e, 223) for e in range(13)}
assert powers3 == {1, 3, 9, 27, 81, 20, 60, 180, 94, 59, 177, 85, 32}
for target, normalized in [(167, [167, 30, 191]),
                           (112, [112, 163, 64])]:
    assert normalized == [(target * pow(13, -j, 223)) % 223 for j in range(3)]
    assert not (powers3 & set(normalized))
assert (-pow(4, -1, 223)) % 223 == 167 and -x % 223 == 112

# All five are demonstrably soluble elsewhere; no one-fiber obstruction is
# an Erdős--Straus counterexample. Strict order and exact fractions checked.
witnesses = [
    (193, 50, 'I', 5),
    (2521, 636, 'II', 8),
    (66529, 16646, 'I', 41),
    (8803369, 2200869, 'II', 121),
    (3361, 841, 'II', 29),
]
for p, x, branch, w in witnesses:
    print('ordered witness:', p, triple(p, x, branch, w))
print('Paired Gaussian / 48B-shift finite audit passed; no universal claim.')
