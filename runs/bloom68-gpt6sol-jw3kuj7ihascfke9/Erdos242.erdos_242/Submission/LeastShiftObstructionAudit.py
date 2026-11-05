#!/usr/bin/env python3
"""Exact finite audit of LeastShiftObstruction.lean and three stress primes.

The Lean file proves the local counterexample; this script independently
checks primality/factorizations by trial division and fraction equalities with
exact rational arithmetic. Finite checks are NOT a universal ESC proof.
"""
from fractions import Fraction
from math import isqrt


def factor(n):
    assert n > 0
    out = {}
    r = 2
    while r * r <= n:
        if n % r == 0:
            power = 0
            while n % r == 0:
                n //= r
                power += 1
            out[r] = power
        r += 1 if r == 2 else 2
    if n > 1:
        out[n] = 1
    return out


def prime(n):
    return n > 1 and factor(n) == {n: 1}


def divisors_of_square(n):
    ds = [1]
    for r, e in factor(n).items():
        ds = [d * r**i for d in ds for i in range(2 * e + 1)]
    assert len(ds) == len(set(ds))
    return sorted(ds)


def divisors(n):
    ds = [1]
    for r, e in factor(n).items():
        ds = [d * r**i for d in ds for i in range(e + 1)]
    return sorted(ds)


def char(r, p):
    assert prime(p) and r % p != 0
    value = pow(r, (p - 1) // 2, p)
    assert value in (1, p - 1)
    return 1 if value == 1 else -1


def full_shift_witnesses(p, u):
    """Every h=4m-1 dividing p+u, and every d|m² with 4d<p."""
    return [(h, m, d)
            for h in divisors(p + u) if h % 4 == 3
            for m in [(h + 1) // 4]
            for d in divisors_of_square(m)
            if 4*d < p and (p + 4*d) % h == 0]


def types(p, x):
    assert p < 4*x and 2*x < p
    a = 4*x - p
    ds = divisors_of_square(x)  # FULL c|x², not just c|x
    return ([c for c in ds if (4*c + 1) % a == 0],
            [d for d in ds if 0 < d < x and (x + d) % a == 0])


def ordered(p, j, branch, v):
    x = (p + 3)//4 + j
    a = 4*x - p
    if branch == 'I':
        c = v
        assert c in types(p, x)[0]
        y = (p*x + x*x//c)//a
        z = (p*x + p*p*c)//a
    else:
        d = v
        assert d in types(p, x)[1]
        y = p*(x + d)//a
        z = p*(x + x*x//d)//a
    assert 1 <= x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    return x, y, z


# p, first shift with any nonresidue prime factor, least nonresidue of p,
# first successful j, branch and full square-divisor certificate at this j.
CASES = (
    (2521, 2, 11, 5, 'II', 8),
    (66529, 5, 13, 4, 'I', 2179447),
    (2784961, 10, 37, 6, 'I', 7823),
)
for p, u0, least_nonres, j0, branch, witness in CASES:
    assert prime(p) and p % 24 == 1
    assert next(r for r in range(1, p) if char(r, p) == -1) == least_nonres
    assert u0 <= least_nonres
    for u in range(1, u0):
        assert all(prime(r) and char(r, p) == 1 for r in factor(p+u))
    factors = factor(p+u0)
    nonres = [r for r in factors if char(r, p) == -1]
    assert nonres
    for j in range(j0):
        assert types(p, (p+3)//4 + j) == ([], []), (p, j)
    triple = ordered(p, j0, branch, witness)
    print(f'p={p}; first nonres factor shift u={u0}, factors={factors},'
          f' nonres factors={nonres}; least nonres={least_nonres};'
          f' first successful j={j0}, {branch}={witness}; ordered={triple}')

assert factor(2784961+10) == {7: 1, 191: 1, 2083: 1}
assert all(char(r, 2784961) == -1 for r in (191, 2083))
assert full_shift_witnesses(2784961, 10) == []
for h, target, possibilities in (
        (7, 6, {1, 2, 4}),
        (191, 98, {2**i * 3**j % 191 for i in range(9) for j in range(3)}),
        (2083, 1044, {1, 521, 651})):
    m = (h + 1)//4
    assert h == 4*m-1 and (2784961+10) % h == 0
    assert (10 * pow(4, -1, h)) % h == target
    assert possibilities == {d % h for d in divisors_of_square(m)}
    assert target not in possibilities
assert all(not full_shift_witnesses(2784961, u) for u in range(1, 16))
assert (767, 192, 4) in full_shift_witnesses(2784961, 16)
for r, x in ((191, 696386), (2083, 697805)):
    assert prime(r) and char(r, 2784961) == -1
    assert x % r == 0 and x - r <= 2784961//4 < x < 2784961//2
    assert types(2784961, x) == ([], []), (r, x)
assert ordered(2784961, 6, 'I', 7823) == (
    696247, 71817878050, 2247303252494450)

assert full_shift_witnesses(2521, 2) == [(87, 22, 44)]
assert (39, 10, 50) in full_shift_witnesses(66529, 5)
assert all(not full_shift_witnesses(66529, u) for u in range(1, 5))

# Perfect squares give only Jacobi 0 or +1; 25 still has Good via Type II.
def jacobi(a, n):
    assert n > 0 and n % 2 == 1
    a %= n
    out = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                out = -out
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            out = -out
        a %= n
    return out if n == 1 else 0

assert all(jacobi(r, 25) in (0, 1)
           for u in range(1, 101) for r in factor(25+u))
assert types(25, 10)[1] == [5]
assert Fraction(4, 25) == Fraction(1, 10) + Fraction(1, 20) + Fraction(1, 100)
print('All finite shift, factor, full-divisor, first-fiber and square checks pass.')
