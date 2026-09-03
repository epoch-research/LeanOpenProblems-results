#!/usr/bin/env python3
"""Finite identity checks for RoughOddMomentResearch.md, not an asymptotic proof.

Uses only the Python standard library. Does not read or edit any Lean file.
"""
from cmath import exp
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, pi, prod


def sieve(N):
    largest = [1] * (N + 1)
    smallest = [N + 1] * (N + 1)
    mu = [1] * (N + 1)
    phi = list(range(N + 1))
    factors = [[] for _ in range(N + 1)]
    largest[0] = 0
    for p in range(2, N + 1):
        if largest[p] == 1:
            for n in range(p, N + 1, p):
                largest[n] = p
                smallest[n] = min(smallest[n], p)
                mu[n] *= -1
                phi[n] -= phi[n] // p
                factors[n].append(p)
            for n in range(p * p, N + 1, p * p):
                mu[n] = 0
    return largest, smallest, mu, phi, factors


MAX_X = 600
P, pmin, mu, phi, fac = sieve(MAX_X * (MAX_X + 1) + 1)
primes = [p for p in range(2, MAX_X + 2) if P[p] == p]


def divisors(n):
    lo, hi = [], []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            lo.append(d)
            if d * d != n:
                hi.append(n // d)
    return lo + hi[::-1]


DIV = [divisors(n) if n else [] for n in range(MAX_X + 2)]


def sgn(n):
    return 1 if P[n + 1] > P[n] else -1


def psi_lt(X, cutoff, d, a):
    return sum(P[m] < cutoff and m % d == a % d for m in range(1, X + 1))


def B_d(X, d):
    return psi_lt(X, pmin[d], d, 1) - 1 - psi_lt(X - 1, pmin[d], d, -1)


def raw_T(X, U, y):
    return sum(
        mu[d] * (psi_lt(X, pmin[d], d, 1) - psi_lt(X, pmin[d], d, -1))
        for d in range(2, U + 1)
        if mu[d] and pmin[d] > y
    )


def check_alladi_and_endpoints():
    cases = 0
    for a in range(1, MAX_X + 1):
        for y in [1, 2, 3, 5, 11, 31]:
            for bound in [1, 2, 5, 13, 37, P[a]]:
                lhs = sum(
                    mu[d] for d in DIV[a]
                    if d > 1 and pmin[d] > y and bound < pmin[d]
                )
                assert lhs == -int(P[a] > max(y, bound)), (a, y, bound, lhs)
                cases += 1
    print(f"Alladi identity: {cases} exact checks passed.")

    cases = 0
    for X in range(2, 241):
        for y in [1, 2, 3, 5, 7, 11, isqrt(X)]:
            Jy = sum(sgn(n) for n in range(1, X) if max(P[n], P[n + 1]) > y)
            t_clean = sum(mu[d] * B_d(X, d) for d in range(2, X + 1)
                          if mu[d] and pmin[d] > y)
            M = sum(mu[d] for d in range(2, X + 1) if pmin[d] > y)
            E = sum(mu[d] for d in DIV[X + 1]
                    if 2 <= d <= X and pmin[d] > y and P[X] < pmin[d])
            assert Jy == t_clean
            assert Jy == raw_T(X, X, y) - M + E
            assert abs(E) <= 2
            cases += 1
    print(f"Clean shifted duality and raw endpoints: {cases} exact checks passed.")


@lru_cache(None)
def local_logs(p):
    prime_divs = fac[p - 1]
    generator = next(g for g in range(2, p)
                     if all(pow(g, (p - 1) // r, p) != 1 for r in prime_divs))
    logs = {}
    a = 1
    for k in range(p - 1):
        logs[a] = k
        a = a * generator % p
    assert len(logs) == p - 1
    return logs


@lru_cache(None)
def characters(d, primitive_only=False):
    """Odd squarefree moduli; returns (conductor, odd, table)."""
    assert d % 2 and mu[d]
    ps = fac[d]
    ranges = [range(1 if primitive_only else 0, p - 1) for p in ps]
    ans = []
    for ks in product(*ranges):
        conductor = prod(p for p, k in zip(ps, ks) if k)
        odd = sum(ks) % 2 == 1
        table = []
        for a in range(d):
            if gcd(a, d) != 1:
                table.append(0j)
            else:
                phase = sum(Fraction(k * local_logs(p)[a % p], p - 1)
                            for p, k in zip(ps, ks))
                table.append(exp(2j * pi * float(phase % 1)))
        ans.append((conductor, odd, tuple(table)))
    assert len(ans) == (prod(p - 2 for p in ps) if primitive_only else phi[d])
    return tuple(ans)


def check_orthogonality_and_conductors():
    cases = 0
    for d in range(3, 101, 2):
        if not mu[d]:
            continue
        chars = characters(d)
        for X in [30, 71, 130]:
            rhs = 2 / phi[d] * sum(
                sum(values[m % d] for m in range(1, X + 1) if P[m] < pmin[d])
                for _, odd, values in chars if odd
            )
            lhs = psi_lt(X, pmin[d], d, 1) - psi_lt(X, pmin[d], d, -1)
            assert abs(lhs - rhs) < 1e-8, (d, X, lhs, rhs)
            cases += 1
        for q, odd, values in chars:
            if odd:
                assert q >= pmin[d]
    print(f"Odd-character orthogonality: {cases} checks passed (tolerance 1e-8).")

    cases = 0
    for X in [40, 80, 140]:
        for U in [20, 50, 90]:
            for y in [2, 3, 5]:
                rhs = 0j
                for q in range(3, U + 1, 2):
                    if not mu[q] or pmin[q] <= y:
                        continue
                    for _, odd, values in characters(q, primitive_only=True):
                        if not odd:
                            continue
                        inner = 0j
                        for m in range(1, X + 1):
                            if P[m] >= pmin[q]:
                                continue
                            W = sum(
                                (Fraction(mu[r], phi[r]) for r in range(1, U // q + 1)
                                 if gcd(r, q) == 1 and pmin[r] > max(y, P[m])),
                                Fraction(0)
                            )
                            inner += values[m % q] * float(W)
                        rhs += 2 * mu[q] / phi[q] * inner
                lhs = raw_T(X, U, y)
                assert abs(lhs - rhs) < 2e-8, (X, U, y, lhs, rhs)
                cases += 1
    print(f"Primitive-conductor regrouping: {cases} checks passed (tolerance 2e-8).")


def closed_counts(X, z, d, a):
    A = sum(P[m] <= z and m % d == a % d for m in range(1, X + 1))
    Fd = sum(P[m] <= z and gcd(m, d) == 1 for m in range(1, X + 1))
    return Fraction(A) - Fraction(Fd, phi[d])


def check_maximal_transfer():
    cases = 0
    for X in [40, 75, 120]:
        for Z0 in [2, 5, 11]:
            ds = [d for d in range(3, X // 2 + 1)
                  if mu[d] and pmin[d] > Z0]
            if not ds:
                continue
            F = [sum(P[m] <= z for m in range(1, X + 1)) for z in range(X + 1)]
            H = sum((Fraction(1, phi[d]) for d in ds), Fraction(0))
            for a in [1, -1]:
                E = {d: [closed_counts(X, z, d, a) for z in range(X + 1)] for d in ds}
                B = max(sum(abs(E[d][z]) for d in ds) for z in range(Z0, X + 1))
                lhs = sum(max(abs(E[d][z]) for z in range(Z0, X + 1)) for d in ds)
                for eta in [Fraction(1, 3), Fraction(1, 7), Fraction(1, 13)]:
                    grid = [Z0]
                    while F[X] - F[grid[-1]] > eta * X:
                        nxt = next(z for z in range(grid[-1] + 1, X + 1)
                                   if F[z] - F[grid[-1]] >= eta * X)
                        grid.append(nxt)
                    if grid[-1] != X:
                        grid.append(X)
                    assert len(grid) <= 1 / eta + 2
                    for u, v in zip(grid, grid[1:]):
                        change = F[v] - F[u]
                        assert change <= eta * X + Fraction(X, Z0)
                        for d in ds:
                            upper = max(abs(E[d][u]), abs(E[d][v])) + Fraction(change, phi[d])
                            assert all(abs(E[d][z]) <= upper for z in range(u, v + 1))
                    rhs = (1 / eta + 2) * B + (eta * X + Fraction(X, Z0)) * H
                    assert lhs <= rhs
                    cases += 1
    print(f"Quantile-grid/maximal-transfer lemma: {cases} rational checks passed.")


def check_prime_and_quadratic_identities():
    cases = 0
    for X in range(3, 401):
        U = isqrt(X)
        pset = [p for p in primes if U < p <= X and p * p > X]
        # Several nontrivial subsets, so the prime-block restriction is tested.
        for subset in [pset, pset[::2], [p for p in pset if p <= X // 3]]:
            pset_now = set(subset)
            lhs = sum(mu[p] * B_d(X, p) for p in subset)
            rhs = sum(X % p == 0 for p in subset)
            # Both large prime factors, when present, are the largest factors.
            rhs += sum(sgn(n) for n in range(1, X)
                       if min(P[n], P[n + 1]) in pset_now
                       and min(P[n], P[n + 1]) ** 2 > X)
            assert lhs == rhs, (X, subset, lhs, rhs)
            cases += 1
    print(f"Exact prime-block identity: {cases} checks passed.")

    cases = 0
    for n in range(1, MAX_X):
        ds = divisors(n * (n + 1))
        for y in [1, 2, 3, 5, 11, 31]:
            rhs = sum(mu[q] * (int(n % pmin[q] == 0) - int((n + 1) % pmin[q] == 0))
                      for q in ds if q > 1 and pmin[q] > y)
            lhs = sgn(n) * int(max(P[n], P[n + 1]) > y)
            assert lhs == rhs, (n, y, lhs, rhs)
            cases += 1
    print(f"Oriented quadratic-root identity: {cases} checks passed.")

def check_small_prime_factorization():
    cases = 0
    for endpoints in [(2, 5, 11, 19), (2, 3, 7, 13), (5, 11, 19, 31)]:
        U, V = endpoints[0], endpoints[-1]
        for n in range(1, MAX_X):
            multiplicities = []
            for p in fac[n]:
                v, r = 0, n
                while r % p == 0:
                    v += 1
                    r //= p
                multiplicities.append((p, v))
            counts = [sum(v for p, v in multiplicities if lo < p <= hi)
                      for lo, hi in zip(endpoints, endpoints[1:])]
            first = next((j for j, count in enumerate(counts) if count), None)
            good = first is not None and counts[first] == 1
            representations = []
            for j, (lo, hi) in enumerate(zip(endpoints, endpoints[1:])):
                for p in primes:
                    if not (lo < p <= hi and n % p == 0):
                        continue
                    rest = n // p
                    if any(U < q <= hi for q in fac[rest]):
                        continue
                    b, c = 1, rest
                    for q in fac[rest]:
                        if q <= U:
                            while c % q == 0:
                                b *= q
                                c //= q
                    assert b * p * c == n and P[b] <= U and (c == 1 or pmin[c] > hi)
                    representations.append((j, b, p, c))
            assert len(representations) == int(good), (n, endpoints, counts, representations)
            if good:
                j, b, p, c = representations[0]
                assert j == first
                for z in [2, 5, 11, 19, 31]:
                    assert int(P[n] <= z) == int(P[b] <= z) * int(p <= z) * int(P[c] <= z)
            else:
                assert not any(counts) or any(count >= 2 for count in counts)
            cases += 1
    print(f"First-occupied-prime-interval factorization: {cases} exact checks passed.")




def check_exponents():
    assert Fraction(17, 36) - Fraction(11, 12) * Fraction(17, 33) == 0
    for epsilon in [Fraction(1, 10), Fraction(1, 100), Fraction(1, 1000)]:
        sigma = epsilon / 40
        allowable = Fraction(17, 36) - Fraction(11, 12) * (Fraction(17, 33) - epsilon / 2) - sigma / 2
        assert allowable > sigma
    print("Dispersion exponent identities and margins: exact rational checks passed.")


if __name__ == "__main__":
    check_alladi_and_endpoints()
    check_orthogonality_and_conductors()
    check_maximal_transfer()
    check_prime_and_quadratic_identities()
    check_small_prime_factorization()
    check_exponents()
    print("PASS: all finite checks. No natural-density claim is inferred from these tests.")
