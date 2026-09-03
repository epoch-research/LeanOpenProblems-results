#!/usr/bin/env python3
"""Sanity checks for BiasAmplificationResearch.md; no Lean dependency.

Finite identities/probabilities use Fraction. Spectral norms, entropy, and a
large binomial tail are floating-point checks of the analytic proofs.
"""
from fractions import Fraction as F
from itertools import product, combinations
from math import comb, exp, lgamma, log, pi, sin, cos
from pathlib import Path
import hashlib
import numpy as np


def sign(x):
    return (x > 0) - (x < 0)


def coupling(lam):
    return [[(1 - lam) / 9 + (lam / 3 if j == (i + 1) % 3 else F(0))
             for j in range(3)] for i in range(3)]


def current(P):
    return sum(P[i][j] * sign(j - i)
               for i in range(len(P)) for j in range(len(P)))


def tensor(P, d):
    states = list(product(range(len(P)), repeat=d))
    ans = []
    for x in states:
        row = []
        for y in states:
            a = F(1)
            for i, j in zip(x, y):
                a *= P[i][j]
            row.append(a)
        ans.append(row)
    return ans


def best_scalar_order(P):
    """Exact maximum current over all strict scalar rankings, by subset DP."""
    n = len(P)
    w = [[P[i][j] - P[j][i] for j in range(n)] for i in range(n)]
    dp = [F(0)] * (1 << n)
    orders = [()] * (1 << n)
    for mask in range(1, 1 << n):
        best = None
        for last in range(n):
            if not (mask >> last) & 1:
                continue
            prev = mask ^ (1 << last)
            val = dp[prev] + sum(w[i][last] for i in range(n)
                                if (prev >> i) & 1)
            if best is None or val > best:
                best = val
                best_order = orders[prev] + (last,)
        dp[mask], orders[mask] = best, best_order
    rank = {v: i for i, v in enumerate(orders[-1])}
    up = sum(P[i][j] for i in range(n) for j in range(n)
             if rank[j] > rank[i])
    down = sum(P[i][j] for i in range(n) for j in range(n)
               if rank[j] < rank[i])
    assert up - down == dp[-1]
    return dp[-1], up, orders[-1]


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B)))
             for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return list(map(list, zip(*A)))


def check_model():
    for lam in (F(1, 5), F(3, 100), F(1, 2)):
        P = coupling(lam)
        assert all(sum(row) == F(1, 3) for row in P)
        assert all(sum(P[i][j] for i in range(3)) == F(1, 3)
                   for j in range(3))
        assert min(x for row in P for x in row) == (1 - lam) / 9
        assert current(P) == lam / 3
        diagonal = sum(P[i][i] for i in range(3))
        continuous_up = sum(P[i][j] for i in range(3)
                            for j in range(i + 1, 3)) + diagonal / 2
        assert continuous_up == (1 + lam / 3) / 2

        alpha = 9 * min(x for row in P for x in row)
        R = [[(P[i][j] - alpha / 9) / (1 - alpha)
              for j in range(3)] for i in range(3)]
        assert alpha == 1 - lam
        assert R == [[F(1, 3) if j == (i + 1) % 3 else F(0)
                      for j in range(3)] for i in range(3)]
        assert current(R) == F(1, 3)
        assert current(P) == (1 - alpha) * current(R)
        assert min(x for row in R for x in row) == 0

        # Exact centered-operator Gram identity on the three-bin alphabet.
        A = [[3 * P[i][j] - F(1, 3) for j in range(3)]
             for i in range(3)]
        gram = matmul(transpose(A), A)
        expected = [[lam**2 * ((1 if i == j else 0) - F(1, 3))
                     for j in range(3)] for i in range(3)]
        assert gram == expected

    lam = F(1, 5)
    P = coupling(lam)
    for d in range(1, 5):
        Pd = tensor(P, d)
        n = 3**d
        K = np.array([[float(n * x) for x in row] for row in Pd])
        centered = K - np.ones((n, n)) / n
        r = np.linalg.svd(centered, compute_uv=False)[0]
        assert abs(r - float(lam)) < 1e-11
        print(f"tensor d={d}: centered operator norm {r:.12f}")
        if d <= 2:
            best, up, _ = best_scalar_order(Pd)
            assert best <= (1 + lam) / 2
            assert up <= (3 + lam) / 4
            print(f"  exact maximum scalar current={best}, ascent={up}")

    # Entropy rate formula for small blocks of the three-bin Markov chain.
    K = [[3 * x for x in row] for row in P]
    h = -sum(float(x) * log(float(x)) for x in K[0])
    assert 0 < h < log(3)
    for L in range(1, 7):
        entropy = 0.0
        for word in product(range(3), repeat=L):
            p = F(1, 3)
            for a, b in zip(word, word[1:]):
                p *= K[a][b]
            entropy -= float(p) * log(float(p))
        assert abs(entropy - (log(3) + (L - 1) * h)) < 1e-11
    print(f"Markov block entropy checked through length 6; rate={h:.12f}")


def check_nonuniform_marginal():
    mu = [F(1, 2), F(1, 3), F(1, 6)]
    eps = F(1, 200)
    C = [[0, 1, -1], [-1, 0, 1], [1, -1, 0]]
    P = [[mu[i] * mu[j] + eps * C[i][j] for j in range(3)]
         for i in range(3)]
    eta = min(P[i][j] / (mu[i] * mu[j])
              for i in range(3) for j in range(3))
    assert eta == F(91, 100)
    W = np.array([[float(P[i][j]) / float(mu[i] * mu[j])**0.5
                   for j in range(3)] for i in range(3)])
    u = np.sqrt(np.array([float(x) for x in mu]))
    r = np.linalg.svd(W - np.outer(u, u), compute_uv=False)[0]
    assert abs(r - 0.03) < 1e-12
    assert r <= float(1 - eta)
    for d in (1, 2):
        best, up, _ = best_scalar_order(tensor(P, d))
        assert best <= 1 - eta / 2
        assert up <= 1 - eta / 4
    print(f"nonuniform marginal tensor check: eta={eta}, norm={r:.12f}")


def check_order_matrix_refinement():
    for q in range(2, 65):
        A = np.array([[sign(j - i) for j in range(q)] for i in range(q)],
                     dtype=float)
        E = np.eye(q) - np.ones((q, q)) / q
        B = E @ A @ E
        explicit = np.array([[0 if i == j else 1 - 2 * ((j - i) % q) / q
                              for j in range(q)] for i in range(q)])
        assert np.max(abs(B - explicit)) < 1e-12
        singular = np.linalg.svd(B, compute_uv=False)
        expected = sorted([0.0] + [abs(cos(pi * j / q) / sin(pi * j / q))
                                  for j in range(1, q)], reverse=True)
        assert np.max(abs(singular - expected)) < 1e-9
        harmonic = sum(1 / j for j in range(1, (q - 1) // 2 + 1))
        assert sum(expected) <= 2 * q / pi * harmonic + 1e-10
    H23 = sum((F(1, j) for j in range(1, 24)), F(0))
    assert H23 == F(444316699, 118982864)
    assert H23 < F(359, 96)
    current_bound = H23 / 50 + F(3, 100) + F(97, 4800)
    assert current_bound < F(1, 8)
    ascent_bound = (1 + current_bound) / 2
    assert ascent_bound < F(9, 16)
    d, eps = 100001, F(1, 100)
    error = exp(-d * float(eps)**2 / 2)
    assert error < 0.01
    disagreement = 1 - error - float(ascent_bound)
    assert disagreement > 0.4275
    print("centered order-matrix spectrum checked for q=2,...,64")
    print(f"epsilon=.01: rational scalar current bound={current_bound} < 1/8")
    print(f"  scalar ascent < 9/16; majority d={d} error <= {error:.12g}")
    print(f"  certified majority/scalar disagreement > {disagreement:.12f}")


def check_majority_and_characters():
    eps = F(1, 15)
    p = (1 + eps) / 2
    for d in range(1, 16, 2):
        up = sum(F(comb(d, k)) * p**k * (1 - p)**(d - k)
                 for k in range(d // 2 + 1, d + 1))
        mean = 2 * up - 1
        assert mean >= eps
        for mask in range(1, 1 << d):
            assert eps ** mask.bit_count() <= eps
        if d == 3:
            assert mean == (3 * eps - eps**3) / 2

    d = 2501
    pf = float(p)
    logs = [lgamma(d + 1) - lgamma(k + 1) - lgamma(d - k + 1)
            + k * log(pf) + (d - k) * log(1 - pf)
            for k in range(d // 2 + 1)]
    m = max(logs)
    error = exp(m) * sum(exp(t - m) for t in logs)
    hoeffding = exp(-d * float(eps)**2 / 2)
    assert 0 < error <= hoeffding < 0.01
    scalar_up_bound = (3 + F(1, 5)) / 4
    disagreement_bound = 1 - float(scalar_up_bound) - hoeffding
    assert disagreement_bound > 0.19
    print(f"independent majority d={d}, epsilon={eps}: error={error:.12g}")
    print(f"  Hoeffding bound={hoeffding:.12g}; scalar ascent <= {scalar_up_bound}")
    print(f"  majority/scalar disagreement >= {disagreement_bound:.12f}")

    # Exhaust all normalized Boolean maps on three bits.
    homomorphisms = []
    for tail in product((0, 1), repeat=7):
        f = (0,) + tail
        if all(f[x ^ y] == (f[x] ^ f[y]) for x in range(8) for y in range(8)):
            homomorphisms.append(f)
    characters = [tuple((x & mask).bit_count() % 2 for x in range(8))
                  for mask in range(8)]
    assert set(homomorphisms) == set(characters)
    assert len(homomorphisms) == 8
    x, y = (-1, -1, 1), (-1, 1, -1)
    xy = tuple(a * b for a, b in zip(x, y))
    assert sign(sum(xy)) != sign(sum(x)) * sign(sum(y))
    print("all 8 normalized Boolean homomorphisms are characters; majority is not")


def largest_prime_factors(M):
    P = [0] * (M + 1)
    P[1] = 1
    for p in range(2, M + 1):
        if P[p] == 0:
            for n in range(p, M + 1, p):
                P[n] = p
    return P


def check_arithmetic_copies():
    N, K = 8000, 80
    P = largest_prime_factors(K * (N + 1))
    count = 0
    for n in range(1, N + 1):
        s = sign(P[n + 1] - P[n])
        assert s != 0
        M = max(P[n], P[n + 1])
        for k in range(1, K + 1):
            copied = sign(P[k * (n + 1)] - P[k * n])
            assert copied == s * (P[k] < M)
            assert copied in (0, s)
            count += 1
    ks = (1, 7, 19, 47, 80)
    original_sum, majority_sum, erased_sources, smooth = 0, 0, 0, 0
    for n in range(1, N + 1):
        original_sum += sign(P[n + 1] - P[n])
        majority_sum += sign(sum(sign(P[k * (n + 1)] - P[k * n]) for k in ks))
        erased_sources += max(P[n], P[n + 1]) <= K
        smooth += P[n] <= K
    assert abs(majority_sum - original_sum) <= 2 * erased_sources <= 2 * smooth
    print(f"raw gap-copy identity checked on {count:,} (n,k) pairs")
    print(f"  exact finite aggregation difference={majority_sum-original_sum}; "
          f"bound={2*erased_sources}")


def check_rearrangement():
    N, a, D = 12, 3, 4
    vals = []
    for A in combinations(range(1, N + 1), D):
        vals.append(sum((F(1, n) for n in A if n >= a), F(0)))
    expected = sum((F(1, n) for n in range(a, a + D)), F(0))
    assert max(vals) == expected
    assert float(expected) <= log(1 + D / a) + 1 / a
    print(f"decreasing-rearrangement extremizer checked: exact weight {expected}")


def main():
    check_model()
    check_nonuniform_marginal()
    check_order_matrix_refinement()
    check_majority_and_characters()
    check_arithmetic_copies()
    check_rearrangement()
    spec = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert digest == "d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb"
    print(f"Spec.lean unchanged: {digest}")
    print("All checks passed.")


if __name__ == "__main__":
    main()
