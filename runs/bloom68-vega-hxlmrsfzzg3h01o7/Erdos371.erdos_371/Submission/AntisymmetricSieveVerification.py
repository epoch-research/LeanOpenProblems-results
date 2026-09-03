#!/usr/bin/env python3
"""Finite algebra checks only; no asymptotic claim is inferred from counts.

This script neither imports nor modifies any Lean specification.
Only Python's standard library is used.
"""
from array import array
from cmath import exp, pi
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
from random import Random

SPEC = Path(__file__).with_name('Spec.lean')
EXPECTED_SPEC = 'd48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb'
assert sha256(SPEC.read_bytes()).hexdigest() == EXPECTED_SPEC


def factors(n):
    n = abs(n)
    assert n >= 1
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def mu_trial(n):
    f = factors(n)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def prime_trial(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def power_floor(x, exponent):
    """Exact floor of x**(numerator/denominator), for exponent in (0,1)."""
    a, b = exponent
    target = x ** a
    lo, hi = 0, x + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** b <= target:
            lo = mid
        else:
            hi = mid
    assert lo ** b <= target < (lo + 1) ** b
    return lo


NMAX = 10**6 + 1
spf = array('I', range(NMAX + 1))
spf[1] = 1
for p in range(2, isqrt(NMAX) + 1):
    if spf[p] == p:
        for n in range(p * p, NMAX + 1, p):
            if spf[n] == n:
                spf[n] = p
lpf = array('I', [0]) * (NMAX + 1)
lam = array('b', [0]) * (NMAX + 1)
mu = array('b', [0]) * (NMAX + 1)
omega = bytearray(NMAX + 1)
lpf[1] = lam[1] = mu[1] = 1
for n in range(2, NMAX + 1):
    p, m = spf[n], n // spf[n]
    lpf[n] = max(p, lpf[m])
    lam[n] = -lam[m]
    mu[n] = 0 if m % p == 0 else -mu[m]
    omega[n] = omega[m] + 1
primes = [n for n in range(2, NMAX + 1) if spf[n] == n]
print('Arithmetic tables through', NMAX, 'built.')

BOX = ((11, 20), (3, 5), (3, 4), (17, 20))
X = 10**6
bounds = tuple(power_floor(X, e) for e in BOX)
zI = power_floor(X, (BOX[1][0], 3 * BOX[1][1]))
zJ = power_floor(X, (BOX[3][0], 3 * BOX[3][1]))
raw_rows = [
    (1, 1999, 59971, (1999,), (59971,)),
    (1, 2137, 64111, (2137,), (61, 1051)),
    (1, 2491, 74731, (47, 53), (74731,)),
    (1, 3763, 112891, (53, 71), (79, 1429)),
    (-1, 2003, 60089, (2003,), (60089,)),
    (-1, 1997, 59909, (1997,), (139, 431)),
    (-1, 3233, 96989, (53, 61), (96989,)),
    (-1, 3551, 106529, (53, 67), (307, 347)),
]
rows = []


def chi3(n):
    return (0, 1, -1)[n % 3]


def rough_data(t, lo, hi, z):
    ds = []
    for u in range(1, isqrt(t) + 1):
        if t % u == 0:
            ds.append(u)
            if u * u != t:
                ds.append(t // u)
    ds = [u for u in ds if lo < u <= hi and spf[u] > z]
    return len(ds), sum(lam[u] for u in ds), sum(lam[t // u] for u in ds)


for eps, p, q, fp, fq in raw_rows:
    assert all(prime_trial(r) for r in (*fp, *fq))
    assert factors(p) == {r: 1 for r in fp}
    assert factors(q) == {r: 1 for r in fq}
    assert q - 30 * p == eps
    assert bounds[0] < p <= bounds[1] < bounds[2] < q <= bounds[3]
    assert p * p > X + 1 and q * q > X + 1
    assert min(fp) > 43 and min(fq) > 43
    assert min(fp) > zI and min(fq) > zJ
    n = 30 * p if eps == 1 else q
    assert 1 <= n <= X and n + 1 <= X
    tau = mu_trial(p * q)
    assert tau in (-1, 1)
    assert mu_trial(n * (n + 1)) == -tau
    assert mu[n] * mu[n + 1] == -tau
    assert p % 6 == eps % 6 and q % 180 == (31 * eps) % 180
    assert n % 180 == (30 if eps == 1 else -31) % 180
    assert chi3(p) == chi3(2 * n + 1) == eps
    assert -chi3(2 * n + 1) * mu_trial(n * (n + 1)) == eps * tau
    rn = -n - 1
    assert rn * (rn + 1) == n * (n + 1)
    assert chi3(2 * rn + 1) == -chi3(2 * n + 1)
    # A reflection-EVEN ambient perturbation has the same positive restriction.
    heven_pos = -chi3(2 * n + 1) * mu_trial(n * (n + 1))
    heven_neg = chi3(2 * rn + 1) * mu_trial(rn * (rn + 1))
    assert heven_pos == heven_neg == eps * tau
    ip, iq = int(len(fp) == 1), int(len(fq) == 1)
    RI, LI, CI = rough_data(n, *bounds[:2], zI)
    RJ, LJ, CJ = rough_data(n, *bounds[2:], zJ)
    RI1, LI1, CI1 = rough_data(n + 1, *bounds[:2], zI)
    RJ1, LJ1, CJ1 = rough_data(n + 1, *bounds[2:], zJ)
    assert (RI, RJ, RI1, RJ1) == ((1, 0, 0, 1) if eps == 1 else (0, 1, 1, 0))
    H = CI * CJ1 - CJ * CI1
    assert H == -eps
    components = (RI * RJ1 - RJ * RI1,
                  LI * RJ1 - RJ * LI1,
                  RI * LJ1 - LJ * RI1,
                  LI * LJ1 - LJ * LI1)
    assert components == (eps, eps * lam[p], eps * lam[q], eps * tau)
    actual_edge = int(bounds[0] < lpf[n] <= bounds[1]) * int(bounds[2] < lpf[n+1] <= bounds[3])
    actual_edge -= int(bounds[2] < lpf[n] <= bounds[3]) * int(bounds[0] < lpf[n+1] <= bounds[1])
    assert actual_edge == eps * ip * iq
    rows.append(dict(eps=eps, p=p, q=q, n=n, tau=tau, ip=ip, iq=iq,
                     components=components, H=H))
print('PASS: all eight actual factorizations, power cutoffs, determinants,')
print('      squarefreeness, rough projection, and H_X(n)=-epsilon.')

local_checks = 0
local_divisors = [r for r in range(1, 129) if lpf[r] <= 43]
local_divisors += [p ** j for p in primes if p <= 43 for j in (2, 3, 4)]
local_divisors = sorted(set(local_divisors))
for eps in (1, -1):
    rr = [r for r in rows if r['eps'] == eps]
    assert [r['tau'] for r in rr] == [1, -1, -1, 1]
    for theta in (-1, 0, 1):
        weights = [1 + theta * eps * r['tau'] for r in rr]
        assert min(weights) >= 0 and max(weights) <= 2
        assert sum(weights) == 4
        assert sum(w * r['ip'] for w, r in zip(weights, rr)) == 2
        assert sum(w * r['iq'] for w, r in zip(weights, rr)) == 2
        assert sum(w * mu[r['p']] for w, r in zip(weights, rr)) == 0
        assert sum(w * mu[r['q']] for w, r in zip(weights, rr)) == 0
        assert sum(w * r['ip'] * r['iq'] for w, r in zip(weights, rr)) == 1 + theta * eps
        for rdiv in local_divisors:
            for sdiv in local_divisors:
                for keys in [('p', 'q'), ('n', 'n1')]:
                    vals = []
                    for r in rr:
                        u = r[keys[0]]
                        v = r['n'] + 1 if keys[1] == 'n1' else r[keys[1]]
                        vals.append(int(u % rdiv == 0 and v % sdiv == 0))
                    assert len(set(vals)) == 1
                    for col in ('one', 'ip', 'iq'):
                        base = [v * (1 if col == 'one' else r[col]) for v, r in zip(vals, rr)]
                        assert sum(w * v for w, v in zip(weights, base)) == sum(base)
                        local_checks += 1
        for key, modulus in [('p', 6), ('q', 180), ('n', 180)]:
            for residue in range(modulus):
                for col in ('one', 'ip', 'iq'):
                    base = [int(r[key] % modulus == residue) * (1 if col == 'one' else r[col]) for r in rr]
                    assert sum(w * v for w, v in zip(weights, base)) == sum(base)
                    local_checks += 1
for theta in (-1, 0, 1):
    w = [1 + theta * r['eps'] * r['tau'] for r in rows]
    assert sum(wi * r['eps'] * r['ip'] * r['iq'] for wi, r in zip(w, rows)) == 2 * theta
    assert sum(wi * mu[r['n']] * mu[r['n'] + 1] for wi, r in zip(w, rows)) == 0
    for residue in range(180):
        even_atom = {residue, (-residue - 1) % 180}
        assert sum(wi * mu[r['n']] * mu[r['n'] + 1] * int(r['n'] % 180 in even_atom)
                   for wi, r in zip(w, rows)) == 0
    assert sum(wi * chi3(2 * r['n'] + 1) * mu[r['n']] * mu[r['n'] + 1] for wi, r in zip(w, rows)) == -8 * theta
    cc = [sum(wi * r['components'][j] for wi, r in zip(w, rows)) for j in range(4)]
    assert cc == [0, 0, 0, 8 * theta]
    for offset in (0, 1):
        for lo, hi in (bounds[:2], bounds[2:]):
            actual = [int(lo < lpf[r['n'] + offset] <= hi) for r in rows]
            assert sum(wi * a for wi, a in zip(w, actual)) == sum(actual)
print('PASS:', local_checks, 'local divisor/residue/marginal equalities.')
print('PASS: weighted pair difference=2 theta; all even local mu tests fixed; odd twisted mu=-8 theta.')
print('PASS: the same positive trade has a globally reflection-even nonnegative extension.')
print('PASS: actual LPF-bin marginals and the first three parity-projection terms unchanged.')

# Embed the same perturbation in the full, unmodified integer candidate interval.
full_pair_counts = {}
for theta in (-1, 0, 1):
    result = {}
    for eps in (1, -1):
        changes = {r['p']: theta * eps * r['tau'] for r in rows if r['eps'] == eps}
        count = 0
        for p in range(bounds[0] + 1, bounds[1] + 1):
            q = 30 * p + eps
            if not (bounds[2] < q <= bounds[3]):
                continue
            count += (1 + changes.get(p, 0)) * int(spf[p] == p) * int(spf[q] == q)
        result[eps] = count
    full_pair_counts[theta] = result[1] - result[-1]
assert full_pair_counts[-1] == full_pair_counts[0] - 2
assert full_pair_counts[1] == full_pair_counts[0] + 2
print('Full fixed-cofactor candidate interval differences, theta=-1,0,1:',
      [full_pair_counts[t] for t in (-1, 0, 1)])


def build_rough(X, lo, hi, z):
    R = array('i', [0]) * (X + 2)
    L = array('i', [0]) * (X + 2)
    C = array('i', [0]) * (X + 2)
    for u in range(lo + 1, hi + 1):
        if spf[u] <= z:
            continue
        assert 1 <= omega[u] <= 2
        for t in range(u, X + 2, u):
            R[t] += 1
            L[t] += lam[u]
            C[t] += lam[t // u]
    return R, L, C


arithmetic_checks = 0
incidence_checks = 0
crt_pair_checks = 0
cases = [(1000, BOX), (1003, BOX), (10000, BOX), (100000, BOX), (1000000, BOX),
         (100000, ((101, 200), (51, 100), (3, 4), (9, 10))),
         (100000, ((3, 5), (13, 20), (4, 5), (9, 10)))]
for X, exps in cases:
    loI, hiI, loJ, hiJ = [power_floor(X, e) for e in exps]
    zI = power_floor(X, (exps[1][0], 3 * exps[1][1]))
    zJ = power_floor(X, (exps[3][0], 3 * exps[3][1]))
    RI, LI, CI = build_rough(X, loI, hiI, zI)
    RJ, LJ, CJ = build_rough(X, loJ, hiJ, zJ)
    FI = bytearray(int(loI < lpf[n] <= hiI) for n in range(X + 2))
    FJ = bytearray(int(loJ < lpf[n] <= hiJ) for n in range(X + 2))
    for n in range(1, X + 2):
        assert 2 * FI[n] == RI[n] - LI[n]
        assert 2 * FJ[n] == RJ[n] - LJ[n]
        assert LI[n] == lam[n] * CI[n]
        assert LJ[n] == lam[n] * CJ[n]
        arithmetic_checks += 4
    c = [0, 0, 0, 0]
    parity = plus = minus = 0
    for n in range(1, X + 1):
        ep = FI[n] * FJ[n + 1]
        em = FJ[n] * FI[n + 1]
        plus += ep
        minus += em
        c[0] += RI[n] * RJ[n + 1] - RJ[n] * RI[n + 1]
        c[1] += LI[n] * RJ[n + 1] - RJ[n] * LI[n + 1]
        c[2] += RI[n] * LJ[n + 1] - LJ[n] * RI[n + 1]
        c[3] += LI[n] * LJ[n + 1] - LJ[n] * LI[n + 1]
        H = CI[n] * CJ[n + 1] - CJ[n] * CI[n + 1]
        parity += lam[n] * lam[n + 1] * H
        # Negative reflection exchanges the absolute values n and n+1.
        reflected_H = CI[n + 1] * CJ[n] - CJ[n + 1] * CI[n]
        assert reflected_H == -H
        arithmetic_checks += 1
        if ep or em:
            eps = 1 if ep else -1
            p = lpf[n] if ep else lpf[n + 1]
            q = lpf[n + 1] if ep else lpf[n]
            m = n // p if ep else (n + 1) // p
            k = (n + 1) // q if ep else n // q
            assert k * q - m * p == eps
            assert gcd(m, k) == 1 and min(m * p, k * q) == n
            assert p * q > 2 * X + 1
            r = p * ((-pow(p, -1, q)) % q)
            reverse = p * q - 1 - r
            assert (r if ep else reverse) == n
            assert (reverse if ep else r) > X
            incidence_checks += 1
    D = plus - minus
    assert 4 * D == c[0] - c[1] - c[2] + c[3]
    assert c[3] == parity
    ps = [p for p in primes if loI < p <= hiI]
    qs = [q for q in primes if loJ < q <= hiJ]
    switched = sum(FI[k * q - 1] - FI[k * q + 1] for q in qs for k in range(1, X // q + 1))
    endpoint = FI[X] * FJ[X + 1]
    assert D == switched + endpoint
    if X <= 10000:
        crtD = 0
        for p in ps:
            for q in qs:
                r = p * ((-pow(p, -1, q)) % q)
                rr = q * ((-pow(q, -1, p)) % p)
                assert r + rr == p * q - 1
                crtD += int(r <= X) - int(rr <= X)
                crt_pair_checks += 1
        assert crtD == D
    print('Whole-block check X=', X, 'exponents=', exps,
          'counts=', (plus, minus), 'D=', D,
          'parity components=', tuple(c), 'switch endpoint=', endpoint)
print('PASS:', arithmetic_checks, 'whole-block divisor/parity/reflection checks,')
print('     ', incidence_checks, 'actual cofactor/CRT incidence checks, and',
      crt_pair_checks, 'exhaustive CRT pair checks.')

# Verify local root counts for both orientations, including obstructed parity.
local_roots = 0
for m in range(1, 21):
    for k in range(1, 21):
        if gcd(m, k) != 1:
            continue
        for ell in [p for p in primes if p <= 31]:
            counts = []
            for eps in (1, -1):
                p0 = (-eps * pow(m, -1, k)) % k if k > 1 else 0
                q0 = (m * p0 + eps) // k
                assert k * q0 - m * p0 == eps
                count = sum(((p0 + k * t) * (q0 + m * t)) % ell == 0 for t in range(ell))
                counts.append(count)
            assert counts == ([1, 1] if m * k % ell == 0 else [2, 2])
            local_roots += 1
print('PASS:', local_roots, 'local root-count sign identities.')

# Finite odd-character orthogonality, with all variables in their actual residue groups.
char_checks = 0
for p in [r for r in primes if 3 <= r <= 43]:
    pp = list(factors(p - 1))
    g = next(g for g in range(2, p) if all(pow(g, (p-1)//r, p) != 1 for r in pp))
    logs = [None] * p
    z = 1
    for j in range(p - 1):
        logs[z] = j
        z = z * g % p
    roots = [exp(2j * pi * j / (p - 1)) for j in range(p - 1)]
    for k in range(1, p):
        for q in range(1, p):
            val = 2 / (p - 1) * sum(roots[(j * (logs[k] + logs[q])) % (p - 1)]
                                     for j in range(1, p - 1, 2))
            expected = int(k * q % p == 1) - int(k * q % p == p - 1)
            assert abs(val - expected) < 1e-12
            char_checks += 1
print('PASS:', char_checks, 'odd-character orthogonality checks (numerical roots only).')

# Balanced factorization: convolution is identically zero at primes beyond sqrt(level).
rng = Random(371)
factor_checks = 0
for R in (2, 5, 11, 23, 50):
    a = [0] + [rng.choice((-1, 0, 1)) for _ in range(R)]
    b = [0] + [rng.choice((-1, 0, 1)) for _ in range(R)]
    conv = [0] * (R * R + 1)
    for u in range(1, R + 1):
        for v in range(1, R + 1):
            conv[u * v] += a[u] * b[v]
    for p in [p for p in primes if R < p <= R * R]:
        assert conv[p] == 0
        factor_checks += 1
print('PASS:', factor_checks, 'balanced-factorization prime-support checks.')
assert sha256(SPEC.read_bytes()).hexdigest() == EXPECTED_SPEC
print('PASS: Spec.lean unchanged:', EXPECTED_SPEC)
print('All finite checks passed. No asymptotic prime-pair claim was tested or assumed.')
