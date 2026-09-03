#!/usr/bin/env python3
"""Finite checks for EpsilonBandPOVMContinuation.md; not a prime theorem.

Only the checksum of Spec.lean is inspected.  No Lean admissions are used.
Analytic proofs in the markdown, not floating-point eigenvalues, establish
fixed-tuple feasibility and the two-site completion.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial, log, sqrt
from pathlib import Path
import hashlib
import numpy as np


def stripe_law(offsets, a, b):
    period = a + b
    endpoints = sorted({Q(0), period} |
                       {x % period for x in offsets} |
                       {(x-a) % period for x in offsets})
    law = {}
    for lo, hi in zip(endpoints, endpoints[1:]):
        u = (lo + hi) / 2
        mask = sum(1 << i for i, x in enumerate(offsets)
                   if (x-u) % period < a)
        law[mask] = law.get(mask, Q(0)) + (hi-lo)/period
    assert sum(law.values()) == 1
    return law


def compressed_tensor(local, states):
    out = np.ones((len(states), len(states)))
    for i, matrix in enumerate(local):
        indices = states[:, i]
        out *= matrix[indices[:, None], indices[None, :]]
    return out


def box_cdf(intervals, cutoff):
    """Exact normalized volume of sum of independent uniform variables <= cutoff."""
    n = len(intervals)
    if n == 0:
        return Q(int(cutoff >= 0))
    widths = [hi-lo for lo, hi in intervals]
    x = cutoff - sum(lo for lo, _ in intervals)
    volume = Q(0)
    for mask in range(1 << n):
        y = x - sum(widths[j] for j in range(n) if mask >> j & 1)
        if y > 0:
            volume += (-1)**mask.bit_count() * y**n
    denominator = Q(factorial(n))
    for width in widths:
        denominator *= width
    result = volume / denominator
    assert 0 <= result <= 1
    return result


def exact_patterns(law, n, states, active_prime, inactive_norm, active_norm):
    """Integrate tensor products A_i (prime) or B_i-A_i (nonprime)."""
    d = len(states)
    result = [np.zeros((d, d)) for _ in range(1 << n)]
    zero = np.zeros_like(active_prime)
    for phase_mask, mass in law.items():
        for outcome in range(1 << n):
            if outcome & ~phase_mask:
                continue
            local = []
            for i in range(n):
                active = bool(phase_mask >> i & 1)
                prime = active_prime if active else zero
                norm = active_norm if active else inactive_norm
                local.append(prime if outcome >> i & 1 else norm-prime)
            result[outcome] += float(mass) * compressed_tensor(local, states)
    return result


def min_eig(matrix):
    return float(np.linalg.eigvalsh((matrix + matrix.T)/2)[0])


def main():
    a, b, p, R, s, q = Q(1), Q(3, 2), Q(2, 5), Q(9, 20), Q(1, 20), Q(1, 4)
    c = 1 / p
    offsets = [Q(0), Q(7, 5), Q(14, 5), Q(21, 5), Q(63, 20), Q(21, 10), Q(21, 20)]
    n = len(offsets)
    law = stripe_law(offsets, a, b)
    edges = [(i, j) for i, j in combinations(range(n), 2)
             if a < abs(offsets[i]-offsets[j]) < b]
    independent = [mask for mask in range(1 << n)
                   if not any(mask >> i & 1 and mask >> j & 1 for i, j in edges)]
    assert len(edges) == 7 and len(independent) == 29
    assert all(mask in independent for mask in law)
    print('Band / support:', 'p =', p, 'R =', R, 's =', s)
    print('C7 edges (zero-based):', edges)
    print('Phase patterns / independent patterns:', len(law), len(independent))

    # A 15-dimensional orthonormal box space wholly within Delta_7(R).
    # The first eight vectors lie in the ordinary Delta_7(1/4).
    h, ell = Q(1, 1000), Q(3, 100)
    intervals = [(Q(0), h), (h, q-(n-1)*h), (p, p+ell)]
    widths = [hi-lo for lo, hi in intervals]
    states = np.zeros((1+2*n, n), dtype=int)
    for i in range(n):
        states[1+i, i] = 1
        states[1+n+i, i] = 2
    for state in states:
        assert sum(intervals[j][1] for j in state) <= R
    for state in states[:1+n]:
        assert sum(intervals[j][1] for j in state) <= q
    v = np.sqrt(np.array([float(x) for x in widths]))
    P = np.outer(v, v)
    eye = np.eye(3)

    # Fixed-tuple Gram calculation on g_i = normalized constant short boxes.
    gamma = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            sigma = sum(mass for mask, mass in law.items()
                        if mask >> i & 1 and mask >> j & 1)
            gamma[i, j] = float(sigma / p**2)
    GminusBB = (gamma-1) * float(h)
    np.fill_diagonal(GminusBB, float(1-R+(n-1)*h/2))
    margin = 1-R-(c-1)*s
    assert margin == Q(19, 40)
    assert min_eig(GminusBB) >= float(margin)-1e-13
    print('Analytic Gram margin:', margin)
    print('Compressed Gram minimum eigenvalue:', min_eig(GminusBB))

    # Explicit normalized, but not tensor-marginal, fixed-tuple frame model.
    b1 = (R-q)/(p-q)
    b0 = (1-p*b1)/(1-p)
    assert b1 == Q(4, 3) and b0 == Q(7, 9)
    B1 = np.diag([1., 1., float(b1)])
    B0 = np.diag([1., 1., float(b0)])
    frame = exact_patterns(law, n, states, float(c)*P, B0, B1)
    norm_error = np.max(np.abs(sum(frame)-np.eye(len(states))))
    frame_min = min(min_eig(M) for M in frame)
    assert norm_error < 1e-12 and frame_min > -1e-12
    assert all(np.max(np.abs(frame[mask])) < 1e-12
               for mask in range(1 << n) if mask not in independent)

    # Exact box integrals for the actual truncated BV forms.
    lower_min = float('inf')
    for i in range(n):
        Ti = np.zeros((len(states), len(states)))
        for row, sr in enumerate(states):
            other = [intervals[sr[j]] for j in range(n) if j != i]
            fraction = float(box_cdf(other, s))
            for col, sc in enumerate(states):
                if all(sr[j] == sc[j] for j in range(n) if j != i):
                    Ti[row, col] = v[sr[i]] * v[sc[i]] * fraction
        Ei = sum(frame[mask] for mask in range(1 << n) if mask >> i & 1)
        lower_min = min(lower_min, min_eig(Ei-Ti))
    assert lower_min > -1e-12
    print('Frame normalization error / min pattern eigenvalue:', norm_error, frame_min)
    print('Frame min eigenvalue of E_i - actual T_i:', lower_min)

    # The exact overlap defect: a long spectator at a forbidden neighbour.
    overlap_h = Q(1, 100)
    discrepancy = (b0-1)*overlap_h
    assert discrepancy == -Q(1, 450)
    print('Frame edge spectator marginal discrepancy:', discrepancy)

    # Universal pair-consistent, cylindrical alternative.
    # w(t)=1 for t<=q; w(t)=(R-t)/(q+R-t) for t>q.
    def long_integral(lo, hi):
        return float(hi-lo) - float(q)*log(float((q+R-lo)/(q+R-hi)))
    vw = v.copy()
    vw[2] = long_integral(*intervals[2]) / sqrt(float(widths[2]))
    Pw = np.outer(vw, vw)
    e = P + float(q)*np.diag([0., 0., 1.])
    Delta = e-Pw
    N = exact_patterns(law, n, states, float(c)*Pw, eye, eye)
    candidate = [M.copy() for M in N]
    for i in range(n):
        local = [eye]*n
        local[i] = Delta
        correction = compressed_tensor(local, states)
        candidate[1 << i] += correction
        candidate[0] -= correction
    candidate_min = min(min_eig(M) for M in candidate)
    K = float(R) - float(q)*log(float(R/q))
    beta = float(R+q-q*q/R) - 2*float(q)*log(float(R/q))
    edge_bound = 2*float(R)*log(2)+float(q)
    assert float(c)*K < 1 and beta < float(p) and edge_bound < 1
    print('Pair K, c*K, ||w||^2, edge norm bound:', K, float(c)*K, beta, edge_bound)
    print('Cylindrical higher-pattern candidate: 15-box minimum eigenvalue:', candidate_min)
    print('Candidate empty / singleton minima:', min_eig(candidate[0]),
          min(min_eig(candidate[1 << i]) for i in range(n)))
    print('(A positive Galerkin check is not an all-F proof.)')
    assert candidate_min > -1e-12
    assert np.max(np.abs(sum(candidate)-np.eye(len(states)))) < 1e-12

    ordinary_error = 0.
    for S in range(1 << n):
        gammaS = (Q(1) if S == 0 else
                  sum(mass for mask, mass in law.items() if mask & S == S)
                  / p**S.bit_count())
        if S:
            assert gammaS <= c**(S.bit_count()-1)
        expected_moment = float(gammaS)*compressed_tensor(
            [P if S >> i & 1 else eye for i in range(n)], states)
        for family in (frame, candidate):
            moment = sum(family[mask] for mask in range(1 << n) if mask & S == S)
            ordinary_error = max(ordinary_error, float(np.max(np.abs(
                moment[:n+1, :n+1]-expected_moment[:n+1, :n+1]))))
    assert ordinary_error < 1e-12
    print('All-order ordinary moment maximum error:', ordinary_error)

    rng = np.random.default_rng(14074897)
    entangled = rng.normal(size=len(states))+1j*rng.normal(size=len(states))
    entangled /= np.linalg.norm(entangled)
    probabilities = [float(np.vdot(entangled, M@entangled).real) for M in frame]
    assert min(probabilities) > -1e-12 and abs(sum(probabilities)-1) < 1e-12
    print('Complex entangled frame state: probability sum / minimum:',
          sum(probabilities), min(probabilities))

    # Check the candidate's algebraic tensor marginal identity, separately
    # from positivity.  These full tensor spaces need not lie in the simplex.
    def candidate_on(offset_list):
        size = len(offset_list)
        st = np.array(list(product(range(3), repeat=size)), dtype=int)
        effects = exact_patterns(stripe_law(offset_list, a, b), size, st,
                                 float(c)*Pw, eye, eye)
        for i in range(size):
            local = [eye]*size
            local[i] = Delta
            correction = compressed_tensor(local, st)
            effects[1 << i] += correction
            effects[0] -= correction
        return effects
    EA = candidate_on(offsets[:2])
    EB = candidate_on(offsets[:3])
    marginal_error = max(float(np.max(np.abs(
        sum(EB[D] for D in range(8) if D & 3 == D0)-np.kron(EA[D0], eye))))
        for D0 in range(4))
    assert marginal_error < 1e-12
    print('Candidate tensor marginal identity maximum error:', marginal_error)

    # Exact finite no-go for gluing the entire p-capped stripe core.
    # This uses additional core identities, NOT honest arithmetic inputs.
    h0, l0, eta = Q(1, 100), Q(3, 100), Q(1, 10000)
    lhs = h0*l0
    rhs = p*eta*(1+Q(1, 10))**2
    assert lhs == Q(3, 10000) and rhs == Q(121, 2500000) and lhs > rhs
    print('Fixed-p-core overlap no-go: LHS / RHS:', lhs, rhs)

    expected = '47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123'
    digest = hashlib.sha256(Path(__file__).with_name('Spec.lean').read_bytes()).hexdigest()
    assert digest == expected
    print('Spec.lean unchanged:', digest)
    print('All asserted finite checks passed.')


if __name__ == '__main__':
    main()
