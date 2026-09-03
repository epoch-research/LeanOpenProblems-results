#!/usr/bin/env python3
"""Finite algebra checks for TripleAlgebraResearch.md; no asymptotic inference."""
from collections import defaultdict
from fractions import Fraction as Q
from hashlib import sha256
from itertools import permutations, product
from math import exp, gcd, isqrt, log
from pathlib import Path

import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parent
SPEC_HASH = 'd48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb'
assert sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_HASH
N = 1_000_000
P = np.zeros(2 * N + 3, dtype=np.int64)
rad = np.ones(2 * N + 3, dtype=np.int64)
P[1] = 1
for p in range(2, len(P)):
    if P[p] == 0:
        P[p::p] = p
        rad[p::p] *= p
n = np.arange(1, N + 1, dtype=np.int64)
x, y, z = P[n], P[n + 1], P[2*n + 1]
s = np.sign(P[2:] - P[1:-1])
B = (np.minimum(x, y) < z) & (z < np.maximum(x, y))
r = s[:N] * (~B)
assert np.all(x != y) and np.all(x != z) and np.all(y != z)
assert np.array_equal(s[2*n-1] + s[2*n], 2*s[:N]*B)
for X in [1, 2, 3, 10, 100, 1000, 10000, 100000, N]:
    assert 2*int(r[:X].sum()) == 2*int(s[:X].sum()) - int(s[:2*X+1].sum()) + 1
print(f'PASS: {N:,} exact dyadic/residual identities and finite-sum endpoints.')

# Lower bypasses and the variable-cutoff error support, all in integer arithmetic.
V = (x*x > n+1) & (y*y > n+1) & (z*z <= n+1)
M = x*y*z  # < 2.1e18 throughout this test, so int64 is safe.
active = M > n+1
assert np.all((~V) | ((~B) & active & (x*y > n+1)))
f = P*P <= np.arange(len(P), dtype=np.int64)
vp = (~f[2*n]) & f[2*n+1] & (~f[2*n+2])
J = f[2*n] & f[2*n+1] & f[2*n+2]
A = f[:-1] & f[1:]
assert np.array_equal(vp.astype(int), f[2*n+1].astype(int)
                     - A[2*n].astype(int) - A[2*n+1].astype(int) + J)
band = np.zeros(N, dtype=bool)
for j in (0, 1, 2):
    p2 = P[2*n+j]**2
    band |= (n+1 < p2) & (p2 <= 2*n+j)
assert np.all((V == vp)[1:] | band[1:])
print(f'PASS: {N:,} valley/activity and Boolean identities; cutoff discrepancies lie in the claimed bands.')
for X in [100, 1000, 10000, 100000, N]:
    print('DATA ONLY:', {'X': X, 'R(X)': int(r[:X].sum()),
                         'bypasses': int((~B[:X]).sum()),
                         'active_bypasses': int(((~B[:X]) & active[:X]).sum()),
                         'V(X)': int(V[:X].sum())})

# Stronger high bypasses: exact integer exponent tests, not floating-point cutoffs.
H_indices = []
high_perm_checks = 0
for k in range(2, N+1):
    t0 = k+1
    p, q, zz = int(P[k]), int(P[k+1]), int(P[2*k+1])
    low, high = t0**11, t0**19
    if not low < p**20 <= high:
        continue
    if not (low < q**20 <= high and zz**20 > high):
        continue
    H_indices.append(k)
    mod = p*q*zz
    assert zz > max(p, q) and int(r[k-1]) != 0
    assert mod**20 > t0**41
    coords0, labs0 = (k, k+1, -2*k-1), (p, q, zz)
    for ijk in permutations(range(3)):
        if ijk == (0, 1, 2):
            continue
        la, lb, lc = (labs0[i] for i in ijk)
        if lc == 2:
            continue
        mm = (((-1)%lb)*(mod//lb)*pow(mod//lb, -1, lb)
              + ((lc-1)//2)*(mod//lc)*pow(mod//lc, -1, lc)) % mod
        NN, DD = coords0[ijk[0]], coords0[ijk[1]]-coords0[ijk[0]]
        assert mm > 0 and (DD*mm-NN) % mod == 0 and DD*mm-NN != 0
        assert mod <= abs(DD*mm-NN) <= (3*k+2)*mm+2*k+1
        if k >= 3:
            assert (6*mm)**20 > t0**21
        high_perm_checks += 1
print('PASS: high-bypass superquadratic product and all-permutation polynomial escape:',
      high_perm_checks, 'checks on', len(H_indices), 'exactly counted high bypasses.')
print('DATA ONLY: first high bypasses:',
      [(k, int(P[k]), int(P[k+1]), int(P[2*k+1])) for k in H_indices[:5]])

# The actual parity projector used in the binary theorem: chi_0 is multiplicative.
parity_checks = 0
for Y in [3, 11, 31]:
    gg = lambda k: int(P[k] <= Y)*(k % 2)
    for a0 in range(1, 101):
        for b0 in range(1, 101):
            assert gg(a0*b0) == gg(a0)*gg(b0)
            parity_checks += 1
    for Z in [2, 5, 17]:
        for k in range(1, 1001):
            assert int(k % 2 == 0)*int(P[k] <= Z)*int(P[k+1] <= Y) \
                == int(P[k] <= Z)*gg(k+1)
            parity_checks += 1
for aa, bb, cc in product([0, 1], repeat=3):
    assert aa*bb*cc >= bb-(1-aa)*bb-bb*(1-cc)
print('PASS: fixed-cutoff multiplicativity/parity projector:', parity_checks,
      '; high-bypass Boolean lower bound: 8 cases.')

# Exact fixed-threshold inclusion/exclusion, then exact rational weight transport.
checks = 0
for Y in [2, 3, 5, 11, 31, 97]:
    ff = P <= Y
    AA = ff[:-1] & ff[1:]
    vv = (~ff[n]) & ff[2*n+1] & (~ff[n+1])
    jj = ff[n] & ff[n+1] & ff[2*n+1]
    for X in [1, 2, 11, 31, 100, 301, 1000]:
        assert int(vv[:X].sum()) == int(ff[3:2*X+2:2].sum()) \
            - int(AA[2:2*X+2].sum()) + int(jj[:X].sum())
        checks += 1
print('PASS: fixed-threshold aggregate identities:', checks)

# The intended odd slice and independent rational checks (keep endpoints explicit).
weighted = 0
for L, U in [(1, 1), (1, 10), (2, 10), (7, 40), (29, 35), (50, 100)]:
    lhs = sum((Q(int(r[k-1]), k) for k in range(L, U+1)), Q())
    rhs = (sum((Q(int(s[k-1]), k) for k in range(L, U+1)), Q())
           - sum((Q(int(s[k-1]), k) for k in range(2*L, 2*U+2)), Q())
           - sum((Q(int(s[2*k]), 2*k*(2*k+1)) for k in range(L, U+1)), Q()))
    assert lhs == rhs
    for Y in [2, 5, 11, 31]:
        ff = lambda k: int(P[k] <= Y)
        aa = lambda k: ff(k)*ff(k+1)
        lpair = sum((Q(aa(2*k)+aa(2*k+1), k) for k in range(L, U+1)), Q())
        rpair = (2*sum((Q(aa(k), k) for k in range(2*L, 2*U+2)), Q())
                 + sum((Q(aa(2*k+1), k*(2*k+1)) for k in range(L, U+1)), Q()))
        assert lpair == rpair
        valley = sum((Q((1-ff(k))*ff(2*k+1)*(1-ff(k+1)), k)
                      for k in range(L, U+1)), Q())
        other = sum((Q(ff(2*k+1)-aa(2*k)-aa(2*k+1)
                       +ff(k)*ff(k+1)*ff(2*k+1), k)
                     for k in range(L, U+1)), Q())
        assert valley == other
        weighted += 1
print('PASS: exact rational logarithmic residual and pair-weight corrections:', weighted)

# CRT and cofactor complements, for every ordered small triple with odd third prime.
primes = [p for p in range(2, 48) if P[p] == p]
crt_checks = 0
perm_div_checks = 0
fiber_rows = []
for p, q, rr in permutations(primes, 3):
    if rr == 2:
        continue
    mod = p*q*rr
    t = ((-1 % q)*(mod//q)*pow(mod//q, -1, q)
         + ((rr-1)//2)*(mod//rr)*pow(mod//rr, -1, rr)) % mod
    tm = mod-1-t
    assert 1 < t < mod-1 and 1 < tm < mod-1
    assert t % p == 0 and (t+1) % q == 0 and (2*t+1) % rr == 0
    assert tm % q == 0 and (tm+1) % p == 0 and (2*tm+1) % rr == 0
    a, b, c = t//p, (t+1)//q, (2*t+1)//rr
    assert q*b-p*a == 1 and p*a+q*b == rr*c
    assert tm == q*(p*rr-b)
    assert tm+1 == p*(q*rr-a)
    assert 2*tm+1 == rr*(2*p*q-c)
    if p < q and (rr < p or rr > q):
        hp = bool(P[a] <= p and P[b] <= q and P[c] <= rr)
        hm = bool(P[p*rr-b] <= q and P[q*rr-a] <= p and P[2*p*q-c] <= rr)
        fiber_rows.append((t, tm, hp, hm))
    coords = (t, t+1, -2*t-1)
    labs = (p, q, rr)
    for ijk in permutations(range(3)):
        la, lb, lc = (labs[i] for i in ijk)
        if lc == 2:
            continue
        mperm = (((-1)%lb)*(mod//lb)*pow(mod//lb, -1, lb)
                 + ((lc-1)//2)*(mod//lc)*pow(mod//lc, -1, lc)) % mod
        NN, DD = coords[ijk[0]], coords[ijk[1]]-coords[ijk[0]]
        assert (DD*mperm-NN) % mod == 0
        assert gcd(DD, mod) == 1
        perm_div_checks += 1
    crt_checks += 1
print('PASS: ordered-triple CRT/complement checks:', crt_checks)
print('PASS: all feasible label-permutation bilinear divisibilities:', perm_div_checks)
for X in [10, 30, 100, 1000, 5000]:
    fiber_current = sum(int(hp and t <= X)-int(hm and tm <= X)
                        for t, tm, hp, hm in fiber_rows)
    mask = active[:X] & (x[:X] <= 47) & (y[:X] <= 47) & (z[:X] <= 47)
    mask[0] = False  # n=1 has the convention P(1)=1, not a prime label.
    assert fiber_current == int((r[:X]*mask).sum())
print('PASS: incomplete active triple-fiber current, five independently counted prefixes.')

# Actual reversed-label pairs, including inactive cases and the active uniqueness.
K = 20_000
labels = defaultdict(list)
for k in range(2, K+1):
    labels[int(P[k]), int(P[k+1]), int(P[2*k+1])].append(k)
matched = 0
active_labels = {}
for k in range(2, K+1):
    p, q, rr = int(P[k]), int(P[k+1]), int(P[2*k+1])
    mod = p*q*rr
    if mod > k+1:
        assert (p, q, rr) not in active_labels
        active_labels[p, q, rr] = k
    for m in labels.get((q, p, rr), []):
        assert (k+m+1) % mod == 0
        if mod > k+1:
            assert mod <= k+m+1 <= 2*K+1
        matched += 1
assert tuple(int(P[k]) for k in [2, 3, 5]) == (2, 3, 5)
assert tuple(int(P[k]) for k in [27, 28, 55]) == (3, 7, 11)
for k, m in [(1475, 547637), (8342, 701018)]:
    p, q, rr = int(P[k]), int(P[k+1]), int(P[2*k+1])
    assert (int(P[m]), int(P[m+1]), int(P[2*m+1])) == (q, p, rr)
    assert p*q*rr == k+m+1
    assert int(r[k-1]) == -int(r[m-1]) != 0
assert V[8342-1]
assert 8342 == 2*43*97 and 8343 == 3**4*103 and 16685 == 5*47*71
assert 701018 == 2*41*83*103 and 701019 == 3**2*11*73*97
assert 1402037 == 7**2*13*31*71
print('PASS: actual reversed-label pairs:', matched, 'within the small search, plus two certified nonlocal pairs;',
      'active labels unique:', len(active_labels))
print('PASS: 8342 in V pairs nonlocally with 701018, with labels (97,103,71)/(103,97,71).')
print('PASS: n=2 -> 27 is NOT a largest-factor-preserving triple reflection.')

# Exact six abc rational maps.
t = sp.symbols('n')
coords = (t, t+1, -2*t-1)
expected = [t, -t/(3*t+1), -t-1, -(t+1)/(3*t+2),
            -(2*t+1)/(3*t+1), -(2*t+1)/(3*t+2)]
for perm, want in zip(permutations(coords), expected):
    a, b, c = perm
    got = sp.cancel(a/(b-a))
    assert sp.cancel(got-want) == 0
    assert sp.cancel(c/(b-a)+(2*got+1)) == 0
    den = sp.denom(got)
    assert sp.cancel(sp.diff(got, t)*den**2) in [1, -1]
    for k in range(1, 100):
        val = got.subs(t, k)
        if got == t:
            assert val == k
        else:
            assert val < 0
        if got != t and got != -t-1:
            assert not val.is_integer
print('PASS: all six abc maps, determinants, and positive-integral no-return.')

# Nonnegative unimodular row comparison / Stern-Brocot barrier.
mat_checks = 0
for a, b, c, d in product(range(13), repeat=4):
    if abs(a*d-b*c) != 1:
        continue
    if (a, b, c, d) in [(1, 0, 0, 1), (0, 1, 1, 0)]:
        continue
    assert (a >= c and b >= d) or (a <= c and b <= d)
    for u, v in [(2, 3), (3, 4), (11, 12), (2, 17), (19, 7)]:
        assert abs((a-c)*u+(b-d)*v) >= min(u, v)
    mat_checks += 1
print('PASS: nonnegative unimodular no-return matrices:', mat_checks)

# Radical product and congruence of support-preserving positive lifts.
rad_checks = 0
for k in range(2, 10001):
    a, b, c = int(rad[k]), int(rad[k+1]), int(rad[2*k+1])
    assert gcd(a, b) == gcd(a, c) == gcd(b, c) == 1
    mod = a*b*c
    m = mod-k-1
    assert m % b == 0 and (m+1) % a == 0 and (2*m+1) % c == 0
    rad_checks += 1
print('PASS: termwise radical support congruences:', rad_checks)
print('c0 =', (1-log(2))*(2*log(2)-1), '(analytic constant, not a fitted density)')
kappa = log(20/19)*(2*log(19/11)-1)
assert kappa > 2/585 > 0
print('kappa =', kappa, '> 2/585; eta range upper endpoint =', 2*exp(-.5)-1)
assert sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_HASH
print('PASS: Spec.lean unchanged:', SPEC_HASH)
print('All finite checks passed. No numerical test is used to assert a limiting density.')
