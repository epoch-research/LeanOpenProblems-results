#!/usr/bin/env python3
"""Exact finite checks for ResidualCovarianceResearch.md, not asymptotic evidence."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product

counts = Counter()


def factors(n):
    ans = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0) + 1
    return ans


def mobius(n):
    ff = factors(n)
    return 0 if any(a > 1 for a in ff.values()) else (-1) ** len(ff)


def clean(c):
    return {k: v for k, v in c.items() if v}


# b_z is represented by exact coefficients of formal symbols log(prime).
I, z = (3, 5, 7, 11), 13


def bz(n):
    return {p: sum(p ** j > z for j in range(1, a + 1))
            for p, a in factors(n).items() if p ** a > z}


def J(n):
    return int(all(n % (r * r) for r in I))


def omega(n):
    return sum(n % r == 0 for r in I)


for t in range(1, 4001):
    good = J(t) * int(omega(t) > 0)
    lhs_mu, rhs_mu = good * mobius(t), F(0)
    lhs_b = {p: good * a for p, a in bz(t).items()}
    rhs_b = Counter()
    for r in I:
        if t % r == 0 and (t // r) % r:
            n = t // r
            rhs_mu -= F(mobius(n) * J(n), 1 + omega(n))
            for p, a in bz(n).items():
                rhs_b[p] += F(a * J(n), 1 + omega(n))
            assert bz(t) == bz(n)  # r < z and r does not divide n
            counts['b_z extraction identities'] += 1
    assert lhs_mu == rhs_mu
    assert clean(lhs_b) == clean(rhs_b)
    counts['exact Ramare coefficient identities'] += 2


# Coefficient arrays in Z[T]/(T^q-1): no floating-point roots of unity.
def multiply(a, b, q):
    c = Counter()
    for i, x in a.items():
        for j, y in b.items():
            c[(i + j) % q] += x * y
    return clean(c)


def signed_binomial(h, a, q):
    c = Counter()
    c[(-h * a) % q] += 1
    c[(h * a) % q] -= 1
    return clean(c)


def kl_difference(argument, p, lift):
    """Unnormalized S(1,argument;p)-S(1,-argument;p), lifted to q."""
    c = Counter()
    for x in range(1, p):
        ix = pow(x, -1, p)
        c[lift * ((x + argument * ix) % p)] += 1
        c[lift * ((x - argument * ix) % p)] -= 1
    return clean(c)


for p1, p2 in combinations((5, 7, 11, 13), 2):
    q = p1 * p2
    units = [x for x in range(q) if x % p1 and x % p2]
    inv = {x: pow(x, -1, q) for x in units}
    for c1, c2 in product((1, 2, 3), repeat=2):
        a1 = p2 * pow(c1 * p2, -1, p1)
        a2 = p1 * pow(c2 * p1, -1, p2)
        H = Counter()
        for s1, s2 in product((-1, 1), repeat=2):
            a = (s1 * a1 + s2 * a2) % q
            assert (c1 * a - s1) % p1 == (c2 * a - s2) % p2 == 0
            H[a] += s1 * s2
            counts['CRT classes'] += 1
        assert len(H) == 4 and sum(v * v for v in H.values()) == 4
        for t in range(q):
            expected = sum(s1 * s2 for s1, s2 in product((-1, 1), repeat=2)
                           if (c1 * t - s1) % p1 == (c2 * t - s2) % p2 == 0)
            assert H[t] == expected == H[-t % q]
            counts['four-sign residue and evenness checks'] += 1
        # Keep H sparse after the Counter lookups above.
        H = clean(H)
        primitive = 0
        for h in range(q):
            direct = Counter()
            for t, v in H.items():
                direct[-h * t % q] += v
            factored = multiply(signed_binomial(h, a1, q),
                                signed_binomial(h, a2, q), q)
            assert clean(direct) == factored
            is_unit = h % p1 != 0 and h % p2 != 0
            assert bool(factored) == is_unit
            if is_unit:
                # Neither local pair of complex roots agrees: product is nonzero.
                assert 2 * h * pow(c1 * p2, -1, p1) % p1
                assert 2 * h * pow(c2 * p1, -1, p2) % p2
                primitive += 1
            counts['exact Fourier factorizations'] += 1
        assert primitive == (p1 - 1) * (p2 - 1)

        frequencies = sorted(set((0, 1, 2, p1, p2, p1 + p2, q - 1)))
        for h, k in product(frequencies, repeat=2):
            direct = Counter()
            for a, sign in H.items():
                for x in units:
                    direct[(h * x + k * a * inv[x]) % q] += sign
            arg1 = h * k * pow(c1, -1, p1) * pow(p2, -1, p1) ** 2
            arg2 = h * k * pow(c2, -1, p2) * pow(p1, -1, p2) ** 2
            factored = multiply(kl_difference(arg1, p1, p2),
                                kl_difference(arg2, p2, p1), q)
            assert clean(direct) == factored
            if (h * k) % p1 == 0 or (h * k) % p2 == 0:
                assert not factored
            counts['exact double-completion factorizations'] += 1

        # Direct complete (x,y) transform, to check the route into Kloosterman sums.
        for h, k in ((0, 0), (1, 2), (p1, 1)):
            matrix, hyperbola = Counter(), Counter()
            mass = 0
            for x, y in product(range(q), repeat=2):
                v = H.get(x * y % q, 0)
                matrix[(h * x + k * y) % q] += v
                mass += v * v
            for a, sign in H.items():
                for x in units:
                    hyperbola[(h * x + k * a * inv[x]) % q] += sign
            assert clean(matrix) == clean(hyperbola)
            assert mass == 4 * (p1 - 1) * (p2 - 1)
            counts['direct two-dimensional transform checks'] += 1


# The extra extraction-coprimality restrictions are exact inclusion-exclusion.
for r1, r2, s1, s2 in product((3, 5, 7), repeat=4):
    rp, sp = sorted(set((r1, r2))), sorted(set((s1, s2)))
    rd = [d for d in range(1, r1 * r2 + 1)
          if (r1 * r2) % d == 0 and mobius(d)]
    sd = [d for d in range(1, s1 * s2 + 1)
          if (s1 * s2) % d == 0 and mobius(d)]
    for n, m in product(range(1, 16), repeat=2):
        lhs = int(all(n % r for r in rp) and all(m % s for s in sp))
        rhs = sum(mobius(e) * mobius(f) for e in rd for f in sd
                  if n % e == 0 and m % f == 0)
        assert lhs == rhs
        counts['coprimality inclusion-exclusion checks'] += 1


for p, b, d, v, sign in product((17, 19, 23, 29), range(1, 9),
                              range(4, 13), range(4, 13), (-1, 1)):
    k = b * d * v
    if (k - sign) % p == 0:
        a = (k - sign) // p
        assert a > 0 and a * p - b * d * v == -sign
        assert factors((k - sign) // a) == {p: 1}  # quotient prime retained
        counts['exact divisor switches'] += 1


# Rational power bookkeeping; enumerate every grouping into M0,N1,N2,N3.
P, Q, D, B = F(3, 5), F(9, 10), F(9, 20), F(1, 10)
assert P + F(2, 5) == B + Q == 1
assert (P + Q) / 2 + (P + Q) * F(7, 20) + Q / 4 == F(3, 2)
assert F(1, 18) - F(51, 1000) == F(41, 9000)
assert F(1, 18) + F(28, 9) * F(1, 20) == F(19, 90)
for rho, tau in product((F(j, 4000) for j in range(5)), repeat=2):
    kappa = rho + tau
    n, m, conductor = D - rho, D - tau, 2 * P
    U, V = conductor - n, conductor - m
    assert n + m == Q - kappa
    assert U + V == F(3, 2) + kappa
    assert n + m - conductor == -F(3, 10) - kappa
    assert (n + m) / 2 + rho + tau + B + P == F(23, 20) + kappa / 2
    atomic = (n, m, B, rho, tau)
    best = F(-10)
    for assignment in product(range(4), repeat=5):
        bins = [sum((a for a, j in zip(atomic, assignment) if j == i), F(0))
                for i in range(4)]
        ns = bins[1:]
        allowable = min(min(ns) / 2, F(1, 2) - max(ns),
                        min(x + y for x, y in combinations(ns, 2)) - F(1, 2))
        best = max(best, allowable)
        assert allowable <= F(51, 1000) < F(1, 18)
        counts['Type III atomic groupings'] += 1
    assert best == F(1, 20) + min(rho, tau)
    counts['rational exponent blocks'] += 1

print('PASS: all finite algebraic and exponent checks')
for label, count in sorted(counts.items()):
    print(f'{label}: {count}')
print('No floating-point checks, Spec targets, scale averages, or asymptotic claims.')
