#!/usr/bin/env python3
"""Finite checks accompanying UniformStabilityResearch.md.

The asymptotic assertions are proved in the note, not by this script.
In particular this does NOT numerically establish the missing residue estimate.
Uses only the Python standard library. No files are modified.
"""

from fractions import Fraction as F
import hashlib
import math
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent
SPEC_SHA = "d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb"


def log_interval(x, terms=32):
    """Certified rational lower and upper bounds for log(x), x rational > 1.

    log x = 2 atanh z, z=(x-1)/(x+1).
    Bound the omitted positive terms by a geometric series.
    """
    x = F(x)
    assert x > 1
    z = (x - 1) / (x + 1)
    lo = 2 * sum(z ** (2 * j + 1) / (2 * j + 1) for j in range(terms))
    tail = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return lo, lo + tail


def resonance_certificate():
    l2, u2 = log_interval(2)
    l3, u3 = log_interval(3)
    rho_lower = F(2, 9) + l3 - F(17, 9) * u2
    gamma = F(10, 999)
    osc_lower = 1 - gamma - F(3, 10)
    uniform_diameter = F(102, 151)
    assert rho_lower > F(1155, 100000) > gamma
    assert osc_lower - uniform_diameter > F(1449, 100000)
    assert l2 > F(1, 2)  # F(1/2) = 1-log 2 is not 1/2.
    print("Certified rho(10/3) lower bound:", float(rho_lower))
    print("Certified resonant oscillation lower bound:", float(osc_lower))
    print("Uniform-stability diameter upper limit:", float(uniform_diameter))
    print("Certified strict diameter gap:", float(osc_lower - uniform_diameter))


def block_checks():
    rng = random.Random(371)
    tested = 0
    for blocks in (3, 7, 51):
        for length in (1, 2, 5, 17, 61):
            for ell in (1, 2, 4, 9, 23):
                Y = blocks * length
                u = [rng.uniform(-1, 1) for _ in range(Y + ell + 1)]
                A = [sum(u[m + 1 : m + ell + 1]) / ell for m in range(Y)]
                B = [
                    sum(u[j * length + 1 : (j + 1) * length + 1]) / length
                    for j in range(blocks)
                ]
                C = [
                    sum(A[j * length : (j + 1) * length]) / length
                    for j in range(blocks)
                ]
                assert max(abs(b - c) for b, c in zip(B, C)) <= (ell - 1) / length + 1e-12
                nb = math.sqrt(sum(b * b for b in B) / blocks)
                na = math.sqrt(sum(a * a for a in A) / Y)
                assert nb <= na + (ell - 1) / length + 1e-12
                tested += 1
    print("Nonoverlapping-block finite checks:", tested)


def packet_checks():
    # Exact rational arithmetic, including all floor counts.
    for X, H, L in ((40, 9, 2), (301, 50, 7), (811, 64, 8), (251, 81, 9)):
        Y = X * H
        D = [F(0) for _ in range(Y + 1)]
        for q in range(H + 1, H + L + 1):
            for m in range(q, Y + 1, q):
                D[m] += F(q, L)
        mean = sum(D) / Y
        second = sum(d * d for d in D) / Y
        support = F(sum(d != 0 for d in D), Y)
        assert support <= F(L, H)
        assert 1 - F(2, X) <= mean <= 1
        assert second >= mean * mean / support
        assert second >= (1 - F(2, X)) ** 2 * F(H, L)
        print("Packet X,H,L:", X, H, L, "support:", float(support), "second moment:", float(second))


def largest_factor_sieve(limit):
    P = [0] * (limit + 1)
    P[1] = 1
    for p in range(2, limit + 1):
        if P[p] == 0:
            for n in range(p, limit + 1, p):
                P[n] = p
    f = [0.0] * (limit + 1)
    for n in range(2, limit + 1):
        f[n] = math.log(P[n]) / math.log(n)
    return P, f


def stability_checks(f):
    tests = 0
    max_excess = -1.0
    for n in range(2, 1201):
        for k in range(2, 502):
            excess = abs(f[k * n] - f[n]) - math.log(k) / math.log(k * n)
            assert excess < 1e-12
            max_excess = max(max_excess, excess)
            tests += 1
    assert tests == 599500
    # Sharpness: prime n, power-of-two multiplier.
    for n in (2, 3, 5, 7, 11, 97):
        for a in range(1, 11):
            k = 2 ** a
            if k * n < len(f):
                assert abs(abs(f[k * n] - f[n]) - math.log(k) / math.log(k * n)) < 1e-12
    print("Largest-factor uniform-stability checks:", tests, "max signed excess:", max_excess)


def current_checks(f):
    # phi(t)=t, psi(t)=t^2, Lipschitz-constant sum 3.
    # Centers here may be arbitrary in [0,1] for the finite inequality.
    # They are not numerical estimates of Dickman integrals.
    u = [x - 0.5 for x in f]
    v = [x * x - 0.35 for x in f]

    def j(q, m):
        return u[m] * v[m + q] - v[m] * u[m + q]

    def short_norm(w, L, Y):
        # Starts m=0,...,Y-1, as in the note.
        s = sum(w[1 : L + 1])
        total = 0.0
        for m in range(Y):
            if m:
                s += w[m + L] - w[m]
            total += (s / L) ** 2
        return math.sqrt(total / Y)

    for X, H, L in ((700, 13, 3), (3000, 35, 5), (7000, 81, 9), (2500, 120, 11)):
        Y = X * H
        assert Y + H + L < len(f)
        J1 = sum(j(1, n) for n in range(1, X + 1)) / X
        Js, Bs = [], []
        eta = math.log(2 * H) / (0.5 * math.log(X) + math.log(2 * H))
        for q in range(H + 1, H + L + 1):
            M = Y // q
            Jq = sum(j(q, m) for m in range(1, Y + 1)) / Y
            restricted_sum = sum(j(q, q * n) for n in range(1, M + 1))
            Bq = q * restricted_sum / Y
            assert abs(Bq - (q * M / Y) * (restricted_sum / M)) < 1e-12
            JM = sum(j(1, n) for n in range(1, M + 1)) / M
            assert abs(Bq - JM) <= 6 * eta + 16 / math.sqrt(X) + 4 / X + 1e-12
            assert abs(JM - J1) <= 4 * L / H + 4 / X + 1e-12
            Js.append(Jq)
            Bs.append(Bq)
        R = sum(b - jv for b, jv in zip(Bs, Js)) / L
        # Directly check (11), including its shift H and all end indices.
        swu = sum(u[H + 2 : H + L + 2])
        swv = sum(v[H + 2 : H + L + 2])
        block_expression = 0.0
        for m in range(1, Y + 1):
            if m > 1:
                swu += u[m + H + L] - u[m + H]
                swv += v[m + H + L] - v[m + H]
            block_expression += u[m] * swv / L - v[m] * swu / L
        block_expression /= Y
        assert abs(block_expression - sum(Js) / L) < 1e-11
        bound = (
            short_norm(u, L, Y)
            + short_norm(v, L, Y)
            + 4 * L / H
            + 12 * math.log(2 * H) / math.log(X)
            + 32 / math.sqrt(X)
        )
        assert abs(J1 - R) <= bound + 1e-12
        print("Current X,H,L:", X, H, L, "J1:", J1, "R:", R, "finite bound:", bound)


def digital_checks():
    masses = [F(1, 2 ** (r + 1)) / (1 - F(1, 8)) for r in range(3)]
    assert masses == [F(4, 7), F(2, 7), F(1, 7)]
    current = (masses[0] - masses[2]) / 3
    assert current == F(1, 7)
    assert (1 + current) / 2 == F(4, 7)
    print("Digital model exact limiting signed current:", current)
    print("Digital model exact limiting ascent probability:", (1 + current) / 2)
    for exponent in (10, 14, 18, 20):
        N = 2 ** exponent
        total = 0
        for n in range(N):
            a, b = n.bit_count() % 3, (n + 1).bit_count() % 3
            total += (b > a) - (b < a)
        # Finite prefix state current is the jitter-averaged current, up to a first endpoint.
        assert abs(F(total) - F(N, 7)) <= exponent + 2
        print("Digital prefix:", N, "signed state mean:", total / N)
    for n in range(1, 10000):
        for a in (0, 1, 3, 9):
            assert (n << a).bit_count() % 3 == n.bit_count() % 3
    # Exact failure of fixed-3 stability: binary classes are 1 and 2 along 2^a, 3*2^a.
    for a in range(80):
        assert (2 ** a).bit_count() % 3 == 1
        assert (3 * 2 ** a).bit_count() % 3 == 2
    print("Dyadic invariance and fixed-multiplier-3 obstruction checked.")


def main():
    sha = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert sha == SPEC_SHA, ("Spec.lean has changed", sha)
    print("Spec.lean SHA-256:", sha)
    resonance_certificate()
    block_checks()
    packet_checks()
    _, f = largest_factor_sieve(750000)
    stability_checks(f)
    current_checks(f)
    digital_checks()
    print("All finite checks passed. No asymptotic residue-decoupling estimate is claimed.")


if __name__ == "__main__":
    main()
