#!/usr/bin/env python3
"""Finite algebra checks for AveragedPairWeightAttempt.md.

No search for prime gaps is performed.  The prime lists below are only
moduli for CRT/Ramanujan identities and for the elementary covering sieve.
Asymptotic prime-distribution inputs are not certified by these tests.
"""
from cmath import exp
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import gcd, prod, pi
from random import Random

rng = Random(20260830)
counts = {}


def primes_upto(n):
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, int(p**0.5) + 1))]


def factors(n):
    out = []
    for p in primes_upto(n):
        if n % p == 0:
            out.append(p)
    return out


def mu(n):
    ps = factors(n)
    return 0 if any(n % (p*p) == 0 for p in ps) else (-1)**len(ps)


def phi(n):
    return sum(gcd(a, n) == 1 for a in range(n))


def e(q, a):
    return exp(2j*pi*(a % q)/q)


def close(x, y):
    assert abs(x-y) <= 1e-7 * max(1, abs(x), abs(y)), (x, y)


# The exact primitive-frequency Gram identity.  Coefficients can be signed
# and complex, and multiplying frequencies by a CRT inverse changes nothing.
ncase = 0
for q in (5, 7, 11, 13, 17, 35, 55, 77, 143, 385):
    pmin = min(factors(q))
    for m in range(1, pmin):
        hs = list(range(1, m+1))
        for trial in range(4):
            cs = [complex(rng.randrange(-3, 4), rng.randrange(-2, 3)) for _ in hs]
            Q = next(a for a in range(2, q+2) if gcd(a, q) == 1)
            inv = pow(Q, -1, q)
            lhs = sum(abs(sum(c*e(q, a*inv*h) for c, h in zip(cs, hs)))**2
                      for a in range(q) if gcd(a, q) == 1)
            rhs = (phi(q)-mu(q))*sum(abs(c)**2 for c in cs) + mu(q)*abs(sum(cs))**2
            close(lhs, rhs)
            # Also check full-frequency Parseval, not just the primitive part.
            full = sum(abs(sum(c*e(q, a*h) for c, h in zip(cs, hs)))**2
                       for a in range(q))
            close(full, q*sum(abs(c)**2 for c in cs))
            ncase += 1
counts['Ramanujan/Parseval/CRT-inverse cases'] = ncase


# Exact average of AP discrepancies.  A is arbitrary nonnegative data on
# the reduced classes, not a sequence of primes.  This independently tests
# signs, q versus phi(q), the base CRT residue, and the L2 inequality.
ncase = 0
for q in (5, 7, 11, 13, 35, 77):
    for Q in (2, 3, 8, 15):
        if gcd(Q, q) != 1:
            continue
        for a0 in (1, 2, 5):
            T = 3*q + 4
            ks = list(range(-2, T-2))
            A = {k: rng.randrange(2) if gcd(a0+Q*k, q) == 1 else 0 for k in ks}
            total = sum(A.values())
            cs = [sum(A[k] for k in ks if k % q == c) for c in range(q)]
            U = [c for c in range(q) if gcd(a0+Q*c, q) == 1]
            errors = [F(cs[c]) - (F(total, phi(q)) if c in U else 0) for c in range(q)]
            assert sum(errors) == 0
            ft = [sum(float(errors[c])*e(q, r*c) for c in range(q)) for r in range(q)]
            close(ft[0], 0)
            ps = min(factors(q))
            hs = list(range(1, ps))
            m = len(hs)
            inv = pow(Q, -1, q)
            lhs = sum(errors[(-h-a0)*inv % q] for h in hs)
            rhs = sum(ft[r]*e(q, r*a0*inv)*sum(e(q, r*h*inv) for h in hs)
                      for r in range(q))/q
            close(float(lhs), rhs)
            norm2 = sum(abs(x)**2 for x in ft)
            close(norm2, q*sum(float(x*x) for x in errors))
            bound2 = F(m*(q-m), q*q)*norm2
            assert float(lhs*lhs) <= bound2 + 1e-7
            trivial_norm2 = (T+q)*total
            assert norm2 <= trivial_norm2 + 1e-7
            ncase += 1
counts['exact AP-discrepancy and L2 cases'] = ncase


# Compatible and incompatible core divisors: a prime shared by two
# different offsets larger than all their differences gives zero, not a
# random off-diagonal contribution.  Complete-period CRT counts are exact.
ncase = 0
W, b = 210, 107
for hj, hl, hi in permutations((0, 2, 6), 3):
    assert all(gcd(b+h, W) == 1 for h in (hj, hl, hi))
    for r in (11, 13, 17):
        Q = W*r
        a0 = next(a for a in range(Q) if (a-hj-b) % W == 0 and (a-hj+hi) % r == 0)
        assert gcd(a0, Q) == 1
        for q in (11, 13, 17):
            if gcd(q, Q) == 1:
                a = (a0+Q*((hj-hl-a0)*pow(Q, -1, q) % q)) % (Q*q)
                assert (a-hj-b) % W == 0
                assert (a-hj+hi) % r == 0
                assert (a-hj+hl) % q == 0
                assert gcd(a, Q*q) == 1
                roots = [a0+Q*k for k in range(q) if (a0+Q*k-hj+hl) % q == 0]
                assert roots == [a]
            else:
                assert q == r
                assert (hi-hl) % q != 0
                assert all((a0+Q*k-hj+hl) % q != 0 for k in range(q))
            ncase += 1
counts['compatible/incompatible divisor CRT cases'] = ncase


# Finite separable Maynard expansion and exact without-replacement
# averaging.  Arbitrary signed kernels test the expansion, not positivity
# of its individual cross terms.
ncase = 0
for M in range(2, 7):
    for K in range(1, min(M, 4)+1):
        J = 3
        kernel = [[[rng.randrange(-3, 4) for h in range(M)] for r in range(J)]
                  for i in range(K)]
        tuples = list(permutations(range(M), K))
        direct = sum(sum(prod(kernel[i][r][hs[i]] for i in range(K))
                         for r in range(J))**2 for hs in tuples)
        expanded = sum(sum(prod(kernel[i][r][hs[i]]*kernel[i][s][hs[i]]
                                for i in range(K)) for hs in tuples)
                       for r in range(J) for s in range(J))
        assert direct == expanded
        ncase += 1
for M in range(2, 11):
    for trial in range(30):
        aa = [F(rng.randrange(12), 3) for _ in range(M)]
        S, D = sum(aa), sum(x*x for x in aa)
        without = sum(aa[i]*aa[j] for i in range(M) for j in range(M) if i != j)/F(M*(M-1))
        withrep = S*S/F(M*M)
        assert without == (S*S-D)/F(M*(M-1))
        assert withrep-without == (M*D-S*S)/F(M*M*(M-1))
        assert withrep >= without
        ncase += 1
counts['separable-kernel/injection/diagonal cases'] = ncase


# The minimum Selberg derivative energy on [0,sigma], discretized exactly
# for arbitrary piecewise-linear competitors.  This checks the normalization
# 1/sigma = 2/theta, not 1/(2 theta).
ncase = 0
for den in range(4, 35):
    sigma = F(1, den)
    for pieces in range(1, 9):
        for trial in range(15):
            vals = [F(1)] + [F(rng.randrange(-10, 11), 10) for _ in range(pieces-1)] + [F(0)]
            width = sigma/pieces
            energy = sum((vals[i+1]-vals[i])**2/width for i in range(pieces))
            assert energy >= 1/sigma
            linear = [F(1)-F(i, pieces) for i in range(pieces+1)]
            assert sum((linear[i+1]-linear[i])**2/width for i in range(pieces)) == 1/sigma
            ncase += 1
counts['exact Selberg-energy cases'] = ncase


# The reserve-prime step with a growing protected set.  S is any input
# survivor set meeting the proved capacity hypothesis; the asymptotic
# preliminary sieve supplying S is not simulated.  No CRT row is tested
# for primality or for prime gaps.
ncase = 0
for z in (101, 151, 211, 307, 401, 601):
    C = 2
    primes = primes_upto(z)
    reserve0 = [p for p in primes if p > z/2]
    for omit in (1, 17, reserve0[len(reserve0)//2]):
        reserve = [p for p in reserve0 if p != omit]
        S = sorted(rng.sample(range(1, C*z+1), len(reserve)-1))
        protected = set(S[::2])
        assert len(protected) < min(reserve)
        used = set()
        residues = {}
        for t in S:
            if t in protected:
                continue
            for h in protected:
                assert sum((t-h) % p == 0 for p in reserve) <= 1
            eligible = [p for p in reserve if p not in used and all((t-h) % p for h in protected)]
            assert eligible
            p = eligible[0]
            used.add(p)
            residues[p] = t % p
        for p in reserve:
            if p not in used:
                residues[p] = next(a for a in range(p) if all(h % p != a for h in protected))
        survivors = {t for t in S if all(t % p != a for p, a in residues.items())}
        assert survivors == protected
        ncase += 1
counts['growing-pool reserve-cover cases'] = ncase

for label, n in counts.items():
    print(f'{label}: {n} passed')
print('PASS: all finite algebra checks; no prime-gap search and no asymptotic claim tested.')
