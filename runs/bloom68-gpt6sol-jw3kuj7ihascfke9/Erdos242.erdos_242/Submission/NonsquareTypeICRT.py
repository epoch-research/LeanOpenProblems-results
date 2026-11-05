#!/usr/bin/env python3
"""Exact finite residue-table check for an infinite four-modulus Type-I family.

The mathematical proof is in NonsquareTypeI.md; this verifies its finite CRT
count, its residue subgroups, and a certificate for each covered k mod the
period (with k=0 replaced by k=period if needed).
"""
from NonsquareTypeIIndependent import factor


def nonresidue(n, p):
    return n % p != 0 and pow(n % p, (p - 1) // 2, p) == p - 1


def construction(k):
    n = 24 * k + 1
    assert k > 0
    if n % 5 in (2, 3):
        j, c = (0, 5) if n % 5 == 2 else (1, 5)
    else:
        q, j, divisors = None, None, None
        if nonresidue(n, 7):
            q, j = 7, 1
            divisors = [2**i for i in range(3)]
        elif k % 3 == 1 and nonresidue(n, 11):
            q, j = 11, 2
            divisors = [3**i for i in range(5)]
        elif (k + 1) % 2 == 0 and nonresidue(n, 23):
            q, j = 23, 5
            divisors = [2**i * 3**h for i in range(5) for h in range(3)]
        elif (k + 1) % 3 == 0 and nonresidue(n, 23):
            q, j = 23, 5
            divisors = [2**i * 3**h for i in range(3) for h in range(5)]
        else:
            return None
        qr = {r * r % q for r in range(1, q)}
        assert {d % q for d in divisors} == qr
        x = 6 * k + 1 + j
        assert all(x * x % d == 0 for d in divisors)
        r = next(r for r, e in factor(x) if nonresidue(r, q))
        target = -((q + 1) // 4) % q  # = -inverse(4), for q=4j+3
        d = next(d for d in divisors if (r * d) % q == target)
        c = r * d
    x = 6 * k + 1 + j
    a = 4 * j + 3
    assert n < 4 * x < 2 * n
    assert c > 0 and x * x % c == 0 and (4 * c + 1) % a == 0
    return (x, a, c)


if __name__ == '__main__':
    period = 6 * 5 * 7 * 11 * 23
    tally = {0: 0, 1: 0, 2: 0, 5: 0, None: 0}
    for k in range(1, period + 1):
        w = construction(k)
        if w is None:
            tally[None] += 1
        else:
            j = (4 * w[0] - (24 * k + 1) - 3) // 4
            tally[j] += 1
    assert sum(tally.values()) == period
    assert tally[None] == 10308 and sum(v for j, v in tally.items() if j is not None) == 42822
    print('CRT period=', period, 'first-proof-j counts=', tally,
          'integer density=42822/53130=7137/8855')
    print('prime-class density=83/96 (by PNT in arithmetic progressions)')
