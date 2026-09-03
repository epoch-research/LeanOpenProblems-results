#!/usr/bin/env python3
"""Finite checks for CalibratedEntropyResearch.md; no asymptotic theorem is claimed.

All model probabilities and marginal/copy checks use fractions.Fraction.
Divergences use floating-point natural logarithms, as sanity checks for the
symbolic identities proved in the note. This file does not import or edit Lean.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import product
from math import isclose, log, prod


def close(a, b, tol=2e-11):
    assert isclose(a, b, rel_tol=tol, abs_tol=tol), (a, b)


def entropy(P):
    return -sum(float(v) * log(float(v)) for v in P.values() if v)


def kl(P, Q):
    ans = 0.0
    for key, p in P.items():
        if p:
            q = Q.get(key, F(0))
            assert q > 0, (key, p, q)
            ans += float(p) * log(float(p / q))
    return ans


def mix(P, Q):
    return {k: (P.get(k, F(0)) + Q.get(k, F(0))) / 2
            for k in P.keys() | Q.keys()}


def js(P, Q):
    M = mix(P, Q)
    return (kl(P, M) + kl(Q, M)) / 2


def push(P, f):
    Q = defaultdict(F)
    for x, v in P.items():
        Q[f(x)] += v
    return dict(Q)


def mutual(P):
    A = push(P, lambda z: z[0])
    B = push(P, lambda z: z[1])
    return entropy(A) + entropy(B) - entropy(P)


def transposed(P):
    return push(P, lambda z: (z[1], z[0]))


def K(gamma):
    g = float(gamma)
    return g * log((1 + g) / (1 - g))


def Phi(gamma):
    g = float(gamma)
    return ((1 + g) * log(1 + g) + (1 - g) * log(1 - g)) / 2


def prime_copy_model(primes, gamma):
    """R_i is collapsed to B_i=1_{R_i=0}; independent Bernoulli(1/p_i).

    The omitted nonzero residue labels are independent and uniform and do
    not affect any divergence. D_i=S E_i gives the directed orientation of
    the i-th copy. An independent uniform U in Z/3Z is omitted here.
    """
    n = len(primes)
    P = defaultdict(F)
    for bits in product((0, 1), repeat=n):
        wR = prod(F(1, p) if b else F(p - 1, p)
                  for p, b in zip(primes, bits))
        for s in (-1, 1):
            wS = (1 + s * gamma) / 2
            for e in product((-1, 1), repeat=n):
                wE = F(1)
                for p, b, sign in zip(primes, bits, e):
                    pp = F(1) if b else F(p - 2, 2 * (p - 1))
                    wE *= pp if sign == 1 else 1 - pp
                if not wE:
                    continue
                directions = tuple(s * sign for sign in e)
                # Exact repeated-copy equality on every divisibility event.
                assert all(not b or d == s for b, d in zip(bits, directions))
                P[(bits, directions)] += wR * wS * wE
    P = dict(P)
    Q = push(P, lambda z: (z[0], tuple(-d for d in z[1])))
    assert sum(P.values()) == 1
    return P, Q


def projection(P, indices):
    return push(P, lambda z: (tuple(z[0][i] for i in indices), z[1]))


def check_model(primes, gamma=F(1, 2)):
    P, Q = prime_copy_model(primes, gamma)
    n = len(primes)
    R = push(P, lambda z: z[0])
    D = push(P, lambda z: z[1])
    for bits, weight in R.items():
        expected = prod(F(1, p) if b else F(p - 1, p)
                        for p, b in zip(primes, bits))
        assert weight == expected
    assert all(v == F(1, 2**n) for v in D.values())
    assert D == push(Q, lambda z: z[1])

    # Every individual endpoint is uniform even given ALL residue bits.
    # U is uniform and W=(U,U+1) or its transpose.
    for i in range(n):
        left, right = defaultdict(F), defaultdict(F)
        for (bits, directions), weight in P.items():
            for u in range(3):
                a, b = (u, (u + 1) % 3)
                if directions[i] == -1:
                    a, b = b, a
                left[(bits, a)] += weight / 3
                right[(bits, b)] += weight / 3
        for bits, wr in R.items():
            for a in range(3):
                assert left[(bits, a)] == right[(bits, a)] == wr / 3

    Kjoint, Ajoint = kl(P, Q), js(P, Q)
    hit = 1 - prod(F(p - 1, p) for p in primes)
    assert float(hit) * K(gamma) - 1e-11 <= Kjoint <= K(gamma) + 1e-11
    assert float(hit) * Phi(gamma) - 1e-11 <= Ajoint <= Phi(gamma) + 1e-11

    # If a zero residue is known, one coordinate recovers W exactly, so DPI
    # is equality for the whole conditional law.
    for bits, wr in R.items():
        Pr = {d: v / wr for (r, d), v in P.items() if r == bits}
        Qr = {d: v / wr for (r, d), v in Q.items() if r == bits}
        if any(bits):
            close(kl(Pr, Qr), K(gamma))
            close(js(Pr, Qr), Phi(gamma))

    single_K, single_A = [], []
    for i, p in enumerate(primes):
        Pi, Qi = projection(P, (i,)), projection(Q, (i,))
        ki, ai = kl(Pi, Qi), js(Pi, Qi)
        close(ki, K(gamma) / p + (1 - 1 / p) * K(gamma / (p - 1)))
        close(ai, Phi(gamma) / p + (1 - 1 / p) * Phi(gamma / (p - 1)))
        single_K.append(ki)
        single_A.append(ai)

    chain_K, chain_A = [], []
    previous_K = previous_A = 0.0
    for i in range(n):
        Pi, Qi = projection(P, tuple(range(i + 1))), projection(Q, tuple(range(i + 1)))
        ki, ai = kl(Pi, Qi), js(Pi, Qi)
        chain_K.append(ki - previous_K)
        chain_A.append(ai - previous_A)
        assert chain_K[-1] >= -1e-11
        assert chain_A[-1] >= -1e-11
        previous_K, previous_A = ki, ai
    close(sum(chain_K), Kjoint)
    close(sum(chain_A), Ajoint)

    # Exact redundancy correction: independent residues cease to be
    # independent after observing the pair vector. The orientation-bit
    # experiment has law M=(P+Q)/2; conditioning also on its bit averages
    # the equal total correlations for P and Q.
    def conditional_total_correlation(L):
        hD = entropy(push(L, lambda z: z[1]))
        return sum(entropy(projection(L, (i,))) for i in range(n)) \
            - entropy(L) - (n - 1) * hD
    redundancy = conditional_total_correlation(mix(P, Q)) - conditional_total_correlation(P)
    close(sum(single_A) - Ajoint, redundancy)

    if primes[0] == 2:
        close(chain_K[0], K(gamma))
        close(chain_A[0], Phi(gamma))
        for value in chain_K[1:] + chain_A[1:]:
            close(value, 0)

    wchain = sum(log(p) * d for p, d in zip(primes, chain_K))
    assert log(min(primes)) * Kjoint - 1e-11 <= wchain
    assert wchain <= log(max(primes)) * Kjoint + 1e-11
    print(f"prime-copy model p={primes}, gamma={gamma}")
    print(f"  KL joint={Kjoint:.12f}, sum one-prime KL={sum(single_K):.12f}, base={K(gamma):.12f}")
    print(f"  JS joint={Ajoint:.12f}, sum one-prime JS={sum(single_A):.12f}, base={Phi(gamma):.12f}")
    print("  conditional KL increments=" + repr([round(d, 12) for d in chain_K]))
    print(f"  log-weighted KL: single={sum(log(p)*d for p,d in zip(primes,single_K)):.12f}, chain={wchain:.12f}")
    return Kjoint, sum(single_K)


def circulation(i, j):
    if i == j:
        return 0
    return 1 if j == (i + 1) % 3 else -1


def check_calibration_identity():
    pi = (F(1, 5), F(4, 5))
    mus = ((F(1, 2), F(1, 3), F(1, 6)),
           (F(1, 4), F(1, 3), F(5, 12)))
    eps = F(1, 10000)
    cond = [{(i, j): mu[i] * mu[j] + eps * circulation(i, j)
             for i in range(3) for j in range(3)} for mu in mus]
    for mu, Pr in zip(mus, cond):
        assert min(Pr.values()) > 0
        assert push(Pr, lambda z: z[0]) == dict(enumerate(mu))
        assert push(Pr, lambda z: z[1]) == dict(enumerate(mu))
        assert Pr[(0, 1)] - Pr[(1, 0)] == 2 * eps
    joint = {(r, i, j): pi[r] * cond[r][i, j]
             for r in range(2) for i in range(3) for j in range(3)}
    P = push(joint, lambda z: (z[1], z[2]))
    RAB = push(joint, lambda z: ((z[1], z[2]), z[0]))
    RA = push(joint, lambda z: (z[1], z[0]))
    RB = push(joint, lambda z: (z[2], z[0]))
    lhs = mutual(RAB) - mutual(RA) - mutual(RB)
    rhs = sum(float(w) * mutual(Pr) for w, Pr in zip(pi, cond)) - mutual(P)
    close(lhs, rhs)
    assert lhs < -1e-4

    # Exact Pythagorean splitting of mutual information into reversal-JS
    # and the symmetric pair correlation; here each conditional symmetric
    # law is a product, but the unconditional mixture is not.
    B = mix(P, transposed(P))
    production = sum(float(w) * js(Pr, transposed(Pr)) for w, Pr in zip(pi, cond))
    production -= js(P, transposed(P))
    close(lhs, production - mutual(B))
    assert production >= -1e-12
    print("calibration subtraction with fixed, nonconstant prescribed marginals")
    print(f"  nonzero current={float(2*eps):.8f}; calibrated increment={lhs:.12f}")
    print(f"  antisymmetric production={production:.12f}; symmetric mixture cost={mutual(B):.12f}")

    # The stronger, correctly calibrated reference obeys a genuine KL
    # chain rule. It is distinct from subtracting two marginal costs.
    Qjoint = {(r, i, j): pi[r] * mus[r][i] * mus[r][j]
              for r in range(2) for i in range(3) for j in range(3)}
    Qpair = push(Qjoint, lambda z: (z[1], z[2]))
    residual = kl(joint, Qjoint) - kl(P, Qpair)
    posterior = 0.0
    for (i, j), prob in P.items():
        posterior += float(prob) * kl(
            {r: joint[r, i, j] / prob for r in range(2)},
            {r: Qjoint[r, i, j] / Qpair[i, j] for r in range(2)})
    close(residual, posterior)
    assert residual >= -1e-12
    print(f"  consistent-reference posterior KL={residual:.12f} (nonnegative)")


def check_independent_flip_cost():
    for n in range(1, 8):
        original = {(u, (s,)*n): F(1, 6) for u in range(3) for s in (-1, 1)}
        local_flips = {(u, signs): F(1, 3*2**n)
                       for u in range(3) for signs in product((-1, 1), repeat=n)}
        assert original == push(original, lambda z: (z[0], tuple(-s for s in z[1])))
        close(entropy(local_flips) - entropy(original), (n-1)*log(2))
    print("independent-flip calibration: zero-current copies acquire exactly (m-1) log 2 entropy")


def check_prefix_nonmonotonicity():
    edges = []
    def cycle(sign):
        if sign == 1:
            edges.extend(((0, 1), (1, 2), (2, 0)))
        else:
            edges.extend(((0, 2), (2, 1), (1, 0)))
    for sign in (1, 1, 1, -1, -1, -1, 1, 1):
        cycle(sign)
    vals = []
    for length, gamma in ((12, F(1, 2)), (18, F(0)), (24, F(1, 4))):
        P = {k: F(v, length) for k, v in Counter(edges[:length]).items()}
        assert push(P, lambda z: z[0]) == {i: F(1, 3) for i in range(3)}
        assert push(P, lambda z: z[1]) == {i: F(1, 3) for i in range(3)}
        val = js(P, transposed(P))
        close(val, Phi(gamma))
        vals.append(val)
    assert vals[0] > vals[1] < vals[2]
    print("prefix reversal-JS with EXACT constant marginals at lengths 12,18,24:")
    print("  " + repr([round(v, 12) for v in vals]))


def largest_prime_factors(n):
    out = [1] * (n + 1)
    for p in range(2, n + 1):
        if out[p] == 1:
            for k in range(p, n + 1, p):
                out[k] = p
    return out


def check_frozen_calibration():
    X, y, z = 5000, 13, 71
    lpf = largest_prime_factors(X + y + 1)
    def state(n):
        return 0 if lpf[n] <= y else 1 if lpf[n] <= z else 2
    primes = [p for p in range(2, y + 1) if lpf[p] == p]
    for k in range(1, y + 1):
        for n in range(1, (X + y) // k + 1):
            assert state(k*n) == state(n)
    for p in primes:
        M = X // p
        lifted = Counter((state(p*u), state(p*(u+1))) for u in range(1, M + 1))
        base = Counter((state(u), state(u+1)) for u in range(1, M + 1))
        assert lifted == base
        smooth_y = sum(lpf[u] <= y for u in range(1, M + 1))
        smooth_z = sum(lpf[u] <= z for u in range(1, M + 1))
        assert Counter(state(u) for u in range(1, M + 1)) == Counter(
            {0: smooth_y, 1: smooth_z-smooth_y, 2: M-smooth_z})
    print(f"frozen smooth laws: exact invariance and conditioned gap-p identities checked at X={X}, y={y}, z={z}")


def check_nonuniform_full_support_model():
    primes = (3, 5)
    mu, eps = (F(1, 2), F(1, 3), F(1, 6)), F(1, 100)
    W = {(a, b): mu[a] * mu[b] + eps * circulation(a, b)
         for a in range(3) for b in range(3)}
    assert min(W.values()) > 0
    P = defaultdict(F)
    for bits in product((0, 1), repeat=len(primes)):
        wr = prod(F(1, p) if b else F(p - 1, p) for p, b in zip(primes, bits))
        for e in product((-1, 1), repeat=len(primes)):
            we = F(1)
            for p, b, sign in zip(primes, bits, e):
                pp = F(1) if b else F(p - 2, 2*(p - 1))
                we *= pp if sign == 1 else 1 - pp
            if not we:
                continue
            for pair, w in W.items():
                pairs = tuple(pair if sign == 1 else pair[::-1] for sign in e)
                assert all(not b or z == pair for b, z in zip(bits, pairs))
                P[(bits, pairs)] += wr * we * w
    P = dict(P)
    Q = push(P, lambda x: (x[0], tuple(z[::-1] for z in x[1])))
    R = push(P, lambda x: x[0])
    for i in range(len(primes)):
        for side in (0, 1):
            marginal = push(P, lambda x: (x[0], x[1][i][side]))
            for r, wr in R.items():
                for a in range(3):
                    assert marginal[r, a] == wr * mu[a]
        p = primes[i]
        t = -F(1, p-1)
        Wt = {z: (W[z]+W[z[::-1]])/2 + t*(W[z]-W[z[::-1]])/2 for z in W}
        Pi, Qi = projection(P, (i,)), projection(Q, (i,))
        expected = kl(W, transposed(W))/p + (1-1/p)*kl(Wt, transposed(Wt))
        close(kl(Pi, Qi), expected)
    assert push(P, lambda x: x[1]) == push(Q, lambda x: x[1])
    bound = kl(W, transposed(W))
    hit = 1 - prod(F(p-1, p) for p in primes)
    assert float(hit)*bound - 1e-11 <= kl(P, Q) <= bound + 1e-11
    print("nonuniform full-support extension: arbitrary positive marginal and exact shared copies verified")


def main():
    print("Finite verification; all logarithms are natural.")
    check_frozen_calibration()
    check_calibration_identity()
    joint, summed = check_model((2, 3, 5, 7))
    assert summed > joint
    check_model((3, 5, 7, 11))
    check_model((11, 13, 17, 19))
    check_nonuniform_full_support_model()
    check_independent_flip_cost()
    check_prefix_nonmonotonicity()
    print("PASS: exact probability/marginal/copy checks and numerical KL/JS identities.")


if __name__ == '__main__':
    main()
