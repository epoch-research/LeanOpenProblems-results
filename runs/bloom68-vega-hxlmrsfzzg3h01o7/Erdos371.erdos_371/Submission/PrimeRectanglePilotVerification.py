#!/usr/bin/env python3
"""Finite identity/bookkeeping checks for PrimeRectanglePilotResearch.md.

No project or Lean files are read. These tests do not establish an asymptotic
estimate or a numerical value for its implied constant.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from math import cos, gcd, isclose, log, pi, sin


def sieve(n):
    a = bytearray(b'\1') * (n + 1)
    a[:2] = b'\0\0'
    for p in range(2, int(n**0.5) + 1):
        if a[p]:
            a[p*p:n+1:p] = b'\0' * ((n-p*p)//p + 1)
    return [p for p in range(2, n+1) if a[p]]


PRIMES = sieve(60000)
PRIME_SET = set(PRIMES)


def factor(n):
    out = {}
    for p in PRIMES:
        if p*p > n:
            break
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def divisors(n):
    ds = [1]
    for p, k in factor(n).items():
        old = list(ds)
        for j in range(1, k+1):
            ds += [d * p**j for d in old]
    return ds


def mu(n):
    fs = factor(n)
    return 0 if any(k > 1 for k in fs.values()) else (-1)**len(fs)


def lamvec(n):
    """Lambda(n) as exact coefficients of the formal symbols log(prime)."""
    fs = factor(n)
    return {next(iter(fs)): 1} if len(fs) == 1 else {}


def add(out, vec, c=1):
    for p, k in vec.items():
        out[p] += c*k


def clean(d):
    return {p: k for p, k in d.items() if k}


def proper_powers(lo, hi):
    return [n for n in range(lo+1, hi)
            if len(factor(n)) == 1 and n not in PRIME_SET]


def close(a, b, label):
    assert isclose(a, b, rel_tol=2e-10, abs_tol=2e-9), (label, a, b)


checks = Counter()

# Exact rational reciprocity, not floating-point equality of phases.
for p in PRIMES[:45]:
    for q in PRIMES[45:95]:
        lhs = F(pow(p, -1, q), q) + F(pow(q, -1, p), p)
        assert lhs == 1 + F(1, p*q)
        checks['reciprocity'] += 1

# Vaughan including its small-Lambda term; formal prime logarithms make
# this an exact integer-vector equality rather than a tolerance test.
N = 1500
DS = {n: divisors(n) for n in range(1, N+1)}
MU = {n: mu(n) for n in range(1, N+1)}
LV = {n: lamvec(n) for n in range(1, N+1)}
LOGV = {n: factor(n) for n in range(1, N+1)}
for z in (1, 2, 3, 5, 9, 17, 31):
    for n in range(1, N+1):
        rhs = defaultdict(int)
        if n <= z:
            add(rhs, LV[n])
        for d in DS[n]:
            if d <= z:
                add(rhs, LOGV[n//d], MU[d])
                for b in DS[n//d]:
                    if b <= z:
                        add(rhs, LV[b], -MU[d])
            else:
                for b in DS[n//d]:
                    if b > z:
                        add(rhs, LV[b], MU[d])
        assert clean(rhs) == LV[n], (z, n, clean(rhs), LV[n])
        checks['Vaughan exact vector identities'] += 1

# Periodicity and zero complete mean of every Type I sine kernel;
# also verifies that the inversion involution respects the negative class.
for m in range(3, 70):
    for d in range(1, 20):
        if gcd(d, m) != 1:
            continue
        for h in (1, 2, 5, 11):
            total = 0.0
            for a in range(1, m):
                if gcd(a, m) != 1:
                    continue
                ia = pow(d*a, -1, m)
                ina = pow(d*(-a), -1, m)
                assert (ia + ina) % m == 0
                total += sin(2*pi*h*ia/m)
            close(total, 0.0, ('Type I mean', m, d, h))
            checks['Type I complete means'] += 1

# A mixed prime/prime-power numerator coefficient tests coprimality in
# Parseval, including terms that must be excluded for a prime-power modulus.
b = {}
for n in range(50, 330):
    fs = factor(n)
    if len(fs) == 1:
        k = next(iter(fs.values()))
        b[n] = cos(n*0.17) / k


def residue_data(m, coeff):
    A = defaultdict(float)
    for n, bn in coeff.items():
        if gcd(n, m) == 1:
            A[n % m] += bn
    D = {a: A[a] - A[-a % m] for a in range(1, m)
         if gcd(a, m) == 1}
    return A, D


def sine_sum(m, h, coeff):
    return sum(bn*sin(2*pi*h*pow(n, -1, m)/m)
               for n, bn in coeff.items() if gcd(n, m) == 1)


for m in (4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 25, 27, 32, 49, 64, 81):
    A, D = residue_data(m, b)
    lhs = sum(sine_sum(m, h, b)**2 for h in range(m))
    rhs = (m/4)*sum(x*x for x in D.values())
    close(lhs, rhs, ('inverse-residue Parseval', m))
    checks['inverse-residue Parseval'] += 1

# Full prime sums, with real weights of both signs, for the signed kernel
# and the distinct-prime-modulus CRT identity.
ps = [11, 13, 17, 19, 23]
qs = [q for q in PRIMES if 53 < q < 250]
v = {q: cos(0.071*q) for q in qs}
u = {p: sin(0.23*p) for p in ps}
AD = {p: residue_data(p, v) for p in ps}

for H in (1, 2, 3, 4):
    def C(t):
        return sum(cos(2*pi*h*t) for h in range(1, 2*H+1)) / H

    direct = sum(sum(u[p]*sine_sum(p, h, v) for p in ps)**2
                 for h in range(1, 2*H+1)) / H
    signed = 0.0
    diagonal = 0.0
    crt_total = 0.0
    for p in ps:
        diagonal += u[p]**2 * sum(sine_sum(p, h, v)**2
                                 for h in range(1, 2*H+1)) / H
        for r in ps:
            via_cos = 0.0
            for q in qs:
                tq = pow(q, -1, p)/p
                for s in qs:
                    ts = pow(s, -1, r)/r
                    via_cos += v[q]*v[s]*(C(tq-ts)-C(tq+ts))/2
            product = sum(sine_sum(p, h, v)*sine_sum(r, h, v)
                          for h in range(1, 2*H+1)) / H
            close(via_cos, product, ('cosine subtraction', H, p, r))
            signed += u[p]*u[r]*via_cos
            checks['signed cosine pair expansions'] += 1
            if p == r:
                continue
            Ap, Dp = AD[p]
            Ar, Dr = AD[r]
            unsym = 0.0
            sym = 0.0
            for k in range(1, p*r):
                if gcd(k, p*r) != 1:
                    continue
                x = r*pow(k, -1, p) % p
                y = p*pow(k, -1, r) % r
                unsym += C(k/(p*r))*Ap[x]*(Ar[-y % r]-Ar[y])/2
                sym -= C(k/(p*r))*Dp[x]*Dr[y]/4
                # Verify the CRT reindexing for the sum phase exactly.
                a = pow(x, -1, p)
                bb = pow(y, -1, r)
                assert (r*a + p*bb - k) % (p*r) == 0
                checks['CRT residue bijection instances'] += 1
            close(unsym, product, ('unsymmetrized CRT', H, p, r))
            close(sym, product, ('symmetrized CRT', H, p, r))
            crt_total += u[p]*u[r]*sym
            checks['signed CRT pair identities'] += 1
    close(direct, signed, ('full signed energy', H))
    close(direct, diagonal + crt_total, ('D+O energy', H))
    checks['full energy reconstructions'] += 2

# Sparse collision bound in the numerator prime-power error.
for P, Q in ((40, 200), (65, 600), (100, 2000), (180, 6000), (300, 18000)):
    assert P*P > 2*Q
    pp = [p for p in PRIMES if P < p < 2*P]
    B = proper_powers(Q, 2*Q)
    coll = 0
    for p in pp:
        c = Counter(pow(n, -1, p) for n in B)
        coll += sum(k*k for k in c.values())
    diag = len(pp)*len(B)
    off = 0
    for n in B:
        for nn in B:
            if n == nn:
                continue
            cnt = sum((n-nn) % p == 0 for p in pp)
            assert cnt <= 1
            off += cnt
            checks['proper-power distinct-pair collision bounds'] += 1
    assert coll == diag + off
    assert coll <= diag + len(B)*(len(B)-1)
    checks['proper-power residue norm bounds'] += 1

# A primitive odd character of conductor l^j can be induced only to a
# power of the same l. For each dyadic interval there is at most one such
# power, regardless of j. We verify this structural multiplicity statement.
for P in range(3, 2000):
    lifts = Counter()
    for m in range(P+1, 2*P):
        fs = factor(m)
        if len(fs) != 1:
            continue
        ell, k = next(iter(fs.items()))
        if k < 2:
            continue
        for j in range(1, k+1):
            lifts[ell**j] += 1
    assert all(count <= 1 for count in lifts.values())
    checks['prime-power conductor lift uniqueness'] += 1

# Exact exponent bookkeeping.
p, q, h = F(3, 5), F(9, 10), F(1, 2)
assert 2*p > q and h < p
assert max(F(0), 2*p-h) + max(p+q/2, q) == F(7, 4)
assert p/2 + q + max(2*p, q) - h == F(19, 10)
assert 2*p + q-h == F(8, 5)
assert 3*p + q-h == F(11, 5)
assert (F(11, 5)+F(7, 4))/2 == F(79, 40)
assert p + q/2 == F(21, 20)
A, M, N = h, q, p
bc1 = (M+N)/2 + F(7, 20)*(A+M+N) + max(M, N)/4
bc2 = (M+N)/2 + F(3, 8)*(A+M+N) + (A+max(M, N))/8
assert bc1 == bc2 == F(67, 40)
assert 2*bc1-h == F(57, 20)
assert -F(11, 12)*p + F(17, 36)*q == -F(1, 8)
assert q-2*F(7, 50)-p == F(1, 50)
checks['rational exponent checks'] += 13

print('All finite identity/bookkeeping checks passed:')
for name, n in checks.items():
    print(f'  {name}: {n:,}')
print('TOTAL:', f'{sum(checks.values()):,}')
print('No asymptotic pilot bound or positive eta is asserted by these tests.')
