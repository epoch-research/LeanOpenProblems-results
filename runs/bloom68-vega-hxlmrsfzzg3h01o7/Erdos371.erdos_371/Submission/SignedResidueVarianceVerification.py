#!/usr/bin/env python3
"""Finite checks only; the asymptotic estimate uses Fouvry--Radziwill."""
from fractions import Fraction
from math import gcd


def sieve(N):
    lpf = [0] * (N + 1)
    lpf[1] = 1
    for p in range(2, N + 1):
        if not lpf[p]:
            for n in range(p, N + 1, p):
                lpf[n] = p
    return lpf, [n >= 2 and lpf[n] == n for n in range(N + 1)]


def inverse(a, m):
    return 0 if m == 1 else pow(a, -1, m)


def crt(a, k, b, l):
    d = gcd(k, l)
    assert (b - a) % d == 0
    L = k * (l // d)
    t = ((b - a) // d * inverse(k // d, l // d)) % (l // d)
    q0 = (a + k * t) % L
    assert q0 % k == a % k and q0 % l == b % l
    return q0, L


def variance_case(X, y, lo, hi):
    assert y * y > X + 1 and lo > y
    assert 2 * (X // lo) < y
    lpf, prime = sieve(X + 1)
    F = [int(n >= 1 and lpf[n] <= y) for n in range(X + 2)]
    G = [int(n >= 1 and not F[n]) for n in range(X + 2)]
    full = [0, 0]
    diag = [0, 0]
    factor_off = [0, 0]
    endpoint_checks = 0
    incidence_checks = 0
    for q in range(lo + 1, hi + 1):
        ds = [G[q*m + 1] - G[q*m - 1] for m in range(1, X // q + 1)]
        A = sum(ds)
        assert A == sum(F[q*m - 1] - F[q*m + 1]
                        for m in range(1, X // q + 1))
        B = sum(F[t] for t in range(q - 1, X + 1, q)) \
            - sum(F[t] for t in range(1, X + 1, q))
        endpoint = 1 - (F[X] if (X + 1) % q == 0 else 0) \
                     - (F[X + 1] if X % q == 0 else 0)
        assert A == B + endpoint and abs(endpoint) <= 1
        endpoint_checks += 1
        dq = sum(v*v for v in ds)
        assert q*dq <= X
        full[0] += q*A*A
        diag[0] += q*dq
        if prime[q]:
            full[1] += q*A*A
            diag[1] += q*dq
        for m in range(1, X // q + 1):
            for n in range(1, X // q + 1):
                if m == n:
                    continue
                for e in (-1, 1):
                    for h in (-1, 1):
                        v, w = q*m + e, q*n + h
                        if not (G[v] and G[w]):
                            continue
                        p, r = lpf[v], lpf[w]
                        k, l = v // p, w // r
                        assert p > y and r > y and p != r
                        assert n*k*p - m*l*r == n*e - m*h
                        assert gcd(m, k) == gcd(n, l) == 1
                        assert (n*e - m*h) % gcd(k, l) == 0
                        factor_off[0] += q*e*h
                        if prime[q]:
                            factor_off[1] += q*e*h
                        incidence_checks += 1
    assert full == [diag[j] + factor_off[j] for j in (0, 1)]

    # Independent enumeration after eliminating q by two cofactor congruences.
    switched = [0, 0]
    M, K = X // lo, (X + 1) // y
    family_checks = 0
    for m in range(1, M + 1):
        for n in range(1, M + 1):
            if m == n:
                continue
            upper = min(hi, X // max(m, n))
            if upper <= lo:
                continue
            for k in range(1, K + 1):
                if gcd(m, k) != 1:
                    continue
                for l in range(1, K + 1):
                    if gcd(n, l) != 1:
                        continue
                    d = gcd(k, l)
                    for e in (-1, 1):
                        for h in (-1, 1):
                            if (n*e - m*h) % d:
                                continue
                            q0, L = crt((-e*inverse(m, k)) % k, k,
                                        (-h*inverse(n, l)) % l, l)
                            u, w = m*(L // k), n*(L // l)
                            v, z = (m*q0 + e) // k, (n*q0 + h) // l
                            assert u*z - w*v == (m*h - n*e) // d
                            tmin = max((lo - q0) // L + 1,
                                       (y - v) // u + 1,
                                       (y - z) // w + 1)
                            tmax = (upper - q0) // L
                            family_checks += 1
                            for t in range(tmin, tmax + 1):
                                q, p, r = q0 + L*t, u*t + v, w*t + z
                                assert lo < q <= upper and p > y and r > y
                                assert k*p == m*q + e and l*r == n*q + h
                                if prime[p] and prime[r]:
                                    assert p != r
                                    switched[0] += q*e*h
                                    if prime[q]:
                                        switched[1] += q*e*h
    assert switched == factor_off
    print(f'X={X}, y={y}, q=({lo},{hi}]: X*V(all,prime)={full}; '
          f'X*D={diag}; X*off={switched}; '
          f'checks endpoints/incidences/CRT={endpoint_checks}/{incidence_checks}/{family_checks}')
    return endpoint_checks, incidence_checks, family_checks


def small_prime_factorization_checks():
    N, U = 12000, 3
    ends = [3, 7, 13, 19]
    lpf, prime = sieve(N)
    bins = [[p for p in range(ends[j] + 1, ends[j+1] + 1) if prime[p]]
            for j in range(len(ends) - 1)]
    checked = 0
    for y in [2, 5, 19, 37, 80, 300]:
        F = [int(n >= 1 and lpf[n] <= y) for n in range(N + 1)]
        for n in range(1, N + 1):
            counts = []
            for ps in bins:
                count = 0
                for p in ps:
                    w = n
                    while w % p == 0:
                        count += 1
                        w //= p
                counts.append(count)
            occupied = [j for j, count in enumerate(counts) if count]
            good = bool(occupied and counts[occupied[0]] == 1)
            convolution = 0
            for j, ps in enumerate(bins):
                for p in ps:
                    if p > y or n % p:
                        continue
                    w = n // p
                    if F[w] and all(w % r for prior in bins[:j+1] for r in prior):
                        convolution += 1
            assert convolution == F[n]*good
            assert convolution in (0, 1)
            # The bad-set majorant is no occupied interval or a double incidence.
            assert good or not occupied or any(count >= 2 for count in counts)
            checked += 1
    print('Exact good/bad convolution checks:', checked)
    return checked


def local_and_parameter_checks():
    factors = {}
    triple_roots = {}
    for e in (-1, 1):
        for h in (-1, 1):
            nu = sum(((t+e)*(2*t+h)) % 3 == 0 for t in range(3))
            factors[e, h] = (1 - Fraction(nu, 3)) / (1 - Fraction(1, 3))**2
            triple_roots[e, h] = sum((t*(2*t+e)*(4*t+h)) % 3 == 0
                                     for t in range(3))
            assert factors[e, h] == (Fraction(3, 4) if e == h else Fraction(3, 2))
            assert triple_roots[e, h] == (3 if e == h else 2)
    print('Local two-prime factors at 3:', factors)
    print('Prime-q triple root counts at 3:', triple_roots)
    theta = Fraction(17, 33)
    count = 0
    for c in [Fraction(5001,10000), Fraction(51,100), Fraction(103,200),
              theta - Fraction(1,10000)]:
        a = (Fraction(1,2) + c) / 2
        kappa = (1 + c/theta) / 2
        gap = theta - c/kappa
        for eta in [Fraction(1,2), Fraction(1,10), Fraction(1,100)]:
            sigma = min(a/2, (1-c)/8, eta/4, kappa*gap/100)
            rho = sigma/2
            assert c/theta < kappa < 1 and 0 < rho < sigma
            assert c + 2*sigma < 1 and 2*sigma < eta
            assert sigma/kappa < Fraction(17,36) - Fraction(11,12)*c/kappa - rho
            count += 1
    print('Exact rational parameter-margin checks:', count)
    N = 100
    lpf, prime = sieve(N)
    S, H = Fraction(0), Fraction(0)
    product = Fraction(1)
    for q in range(1, N + 1):
        phi = q
        for p in range(2, q + 1):
            if prime[p] and q % p == 0:
                phi = phi // p * (p-1)
        S += Fraction(q, phi*phi)
        H += Fraction(1, q)
        if prime[q]:
            u = Fraction(q*q, (q-1)*(q-1)) - 1
            product *= 1 + u/q
    assert S <= H*product
    print('Totient reciprocal-square Euler-product majorant verified at N=100.')


if __name__ == '__main__':
    totals = [0, 0, 0]
    for args in [(400,30,45,130), (899,40,70,350),
                 (997,60,80,400), (2100,100,160,800), (4000,80,160,640)]:
        values = variance_case(*args)
        totals = [x+y for x, y in zip(totals, values)]
    small_prime_factorization_checks()
    local_and_parameter_checks()
    print('TOTAL endpoint/incidence/CRT checks:', totals)
    print('All finite checks passed. No asymptotic theorem is inferred from these checks.')
