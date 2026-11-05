#!/usr/bin/env python3
"""Independent explicit-divisor spot audit of NonsquareTypeIAudit.cpp.

Does not certify its entire 10^10 range: the C++ program performs that
exhaustive bounded check. This one enumerates ALL c | x^2 literally, rather
than using the C++ residue-set dynamic program. Uses Python integers only.
"""
from math import isqrt
from random import Random


def factor(n):
    assert n > 0
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            result.append((p, e))
        p += 1 if p == 2 else 2
    if n > 1:
        result.append((n, 1))
    return result


def full_squared_divisors(x):
    divs = [1]
    for p, e in factor(x):
        divs = [d * p**j for d in divs for j in range(2 * e + 1)]
    assert len(divs) == len(set(divs))
    assert all(x * x % d == 0 for d in divs)
    return divs


def first_witness(n, max_j=None):
    assert n > 1 and n % 24 == 1
    k = (n - 1) // 24
    x0 = 6 * k + 1
    bound = min(6 * k, max_j if max_j is not None else 6 * k)
    for j in range(bound):
        x = x0 + j
        a = 4 * j + 3
        assert n < 4 * x < 2 * n
        for c in full_squared_divisors(x):
            if (4 * c + 1) % a == 0:
                return (j, x, a, c)
    return None


if __name__ == '__main__':
    squares = nonsquares = 0
    for n in range(25, 30001, 24):
        square = isqrt(n)**2 == n
        w = first_witness(n, None if square else 40)
        if square:
            squares += 1
            assert w is None, (n, w)
        else:
            nonsquares += 1
            assert w is not None, n
    print('EXPLICIT_SMALL max_n=30000 squares=', squares,
          'nonsquares=', nonsquares)

    for n, expected_j in [(28441, 17), (3153865, 39), (8803369, 37),
                          (9238009, 27), (5346961, 23),
                          (9999999985, None)]:
        if n % 24 != 1:
            continue
        w = first_witness(n, 40)
        assert w and (expected_j is None or w[0] == expected_j), (n, w)
        print('EXTREMAL', n, 'factorization=', factor(n), 'j,x,a,c=', w)

    rng = Random(240242)
    ks = [(10**10 - 1) // 24 - rng.randrange(1000000)
          for _ in range(1000)]
    for k in ks:
        n = 24 * k + 1
        if isqrt(n)**2 == n:
            continue
        assert first_witness(n, 40) is not None, n
    print('EXPLICIT_SAMPLE 1000 deterministic inputs near 10^10 all hit')
