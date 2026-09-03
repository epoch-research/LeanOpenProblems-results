#!/usr/bin/env python3
"""Exact finite audits for CubeEdgePressureResolutionAttempt.md.

This does NOT test or establish summed EL.  The example is a bad pinned
sector in an actual minimizer, not a counterexample to EL.
Run from the project root with python3 Submission/check_cube_edge_pressure_resolution.py.
SciPy is used only to audit one integer minimum-cost matching; the remaining
checks use the standard library.
"""
from collections import Counter
from itertools import product
from math import comb, exp, log, log1p
from pathlib import Path
import hashlib

SPEC_SHA = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def dual(x, n):
    """B(x,v) = parity(dual(x)&v), standard consecutive symplectic pairs."""
    even = sum(1 << i for i in range(0, n, 2))
    return ((x & even) << 1) | ((x >> 1) & even)


def symp(x, v, n):
    return (dual(x, n) & v).bit_count() & 1


def small_cube_audit():
    n, N = 4, 16
    nbr = [sum(1 << y for y in range(N) if symp(x, y, n)) for x in range(N)]
    ordered_edges = sum(x.bit_count() for x in nbr)
    assert ordered_edges == N * (N - 1) // 2
    # Q_3, with even vertices [000,011,101,110] and odd [001,010,100,111].
    evens, odds = [0, 3, 5, 6], [1, 2, 4, 7]
    source_neighbours = [
        [i for i, x in enumerate(evens) if (x ^ y).bit_count() == 1]
        for y in odds
    ]
    assert 0 in source_neighbours[0]
    rooted = [[0] * N for _ in range(N)]
    hom = 0
    for xs in product(range(N), repeat=4):
        lists = []
        for inds in source_neighbours:
            mask = (1 << N) - 1
            for i in inds:
                mask &= nbr[xs[i]]
            lists.append(mask)
        counts = [q.bit_count() for q in lists]
        mult = counts[1] * counts[2] * counts[3]
        hom += counts[0] * mult
        mask = lists[0]
        while mask:
            bit = mask & -mask
            y = bit.bit_length() - 1
            rooted[xs[0]][y] += mult
            mask -= bit
    values = {rooted[x][y] for x in range(N) for y in range(N) if symp(x, y, n)}
    assert len(values) == 1
    assert all(rooted[x][y] == 0 for x in range(N) for y in range(N) if not symp(x, y, n))
    assert next(iter(values)) * ordered_edges == hom
    # Independent C4 trace formula from A^2 = (N/4)(J+I) on nonzero vectors.
    hom_c4 = 0
    for x in range(N):
        for z in range(N):
            hom_c4 += (nbr[x] & nbr[z]).bit_count() ** 2
    assert hom_c4 == N * N * (N * N + N - 2) // 16
    # Monotonicity a_3 >= a_2, checked without roots or floating arithmetic.
    # e_3=12,e_2=4: t_3 >= t_2^3.
    assert hom * N**4 >= hom_c4**3
    print(f"Q3 on Sp(4,2): hom={hom}; rooted oriented-edge counts={values}; {ordered_edges} edges")
    print(f"Q2 exact trace count={hom_c4}; a3>=a2 checked by integers")


def rank_finner_audit():
    cases = 0
    for j in range(1, 9):
        for n in range(2*j, 2*j + 7):
            counts = []
            for r in range(j + 1):
                num, den = 1, 1
                for i in range(r):
                    num *= ((1 << n) - (1 << i)) * ((1 << j) - (1 << i))
                    den *= (1 << r) - (1 << i)
                assert num % den == 0
                counts.append(num // den)
            total = 1 << (n*j)
            assert sum(counts) == total
            weighted = sum(counts[r] * (1 << (j*(j-r))) for r in range(j + 1))
            scale = 1 << (n - 2*j)
            assert weighted * scale <= total * (scale + 4)
            for ell in range(1, j + 1):
                tail = sum(counts[:j-ell+1])
                assert tail * (1 << (ell*(n-j+ell))) <= 4 * total
            cases += 1
    print(f"Rank/Finner input: {cases} exact random-matrix rank distributions and moment bounds checked")


def histogram(k):
    d, r, b = 4 * k, 3 * k, 1 << k
    m, s = 1 << (d - 1), 4 * b
    ns = [s]
    for j in range(1, r + 1):
        left = comb(r - 1, j) if j <= r - 1 else 0
        right = comb(r - 1, j - 1)
        ns.append(2 * (s * left + (s - 1) * right))
    L0 = (2 * s - 1) * (1 << (r - 1))
    assert 2 * L0 - s == sum(ns)
    remaining, cost, J = m, 0, 0
    for j, count in enumerate(ns):
        take = min(remaining, count)
        cost += j * take
        remaining -= take
        if remaining == 0:
            J = j
            break
    assert remaining == 0
    return m, s, ns, L0, cost, J


def exact_pinned_audit():
    k, d, n = 2, 8, 12
    N, h = 1 << n, 1 << d
    m, s, expected, L0, cheapest, J = histogram(k)
    source_evens = [x for x in range(h) if x.bit_count() % 2 == 0]
    source_odds = [x for x in range(h) if x.bit_count() % 2 == 1]
    # E has basis e_i+e_(d-1); f(E) is the affine hyperplane of odd integers <2^d.
    f = {x: 1 | ((x & ((1 << (d - 1)) - 1)) << 1) for x in source_evens}
    pinned = set(f.values())
    assert len(pinned) == m
    assert pinned == set(range(1, h, 2))
    expected_L = {2 | (z << d) for z in range(1 << (n - d))}
    assert len(expected_L) == s and not (expected_L & pinned)
    xs = [v for v in range(N) if v not in pinned]
    col_cost = {}
    accesses = Counter()
    rows = []
    all_endpoint_lists = []
    for y in source_odds:
        ds = [dual(f[y ^ (1 << i)], n) for i in range(d)]
        row = {}
        endpoint = set()
        for v in xs:
            bits = [(q & v).bit_count() & 1 for q in ds]
            if all(bits[:k]):
                cost = sum(1 - z for z in bits[k:])
                row[v] = cost
                if v in col_cost:
                    assert col_cost[v] == cost, "cost must depend only on the host column"
                col_cost[v] = cost
                accesses[v] += 1
                if cost == 0:
                    endpoint.add(v)
        assert len(row) == L0
        assert endpoint == expected_L
        rows.append(row)
        all_endpoint_lists.append(endpoint)
    observed = Counter(col_cost.values())
    assert [observed[j] for j in range(d - k + 1)] == expected
    assert all(accesses[v] == (m if v in expected_L else m // 2) for v in col_cost)
    assert m / L0 < 1  # uniform row marginals satisfy every column capacity at T=0
    assert s < m       # identical endpoint lists violate Hall
    # Integer assignment audit of the exact minimum-cost formula.
    try:
        import numpy as np
        from scipy.optimize import linear_sum_assignment
    except ImportError:
        print("SciPy unavailable: integer assignment audit skipped (histogram identities checked)")
    else:
        mat = np.full((m, len(xs)), 10**6, dtype=np.int64)
        index = {v: i for i, v in enumerate(xs)}
        for i, row in enumerate(rows):
            for v, cost in row.items():
                mat[i, index[v]] = cost
        ii, jj = linear_sum_assignment(mat)
        assert len(ii) == m and len(set(jj)) == m
        costs = [int(mat[i, j]) for i, j in zip(ii, jj)]
        assert max(costs) < 10**6
        assert sum(costs) == cheapest
        print(f"Integer matching audit: exact minimum bad-outer-edge cost={cheapest}, threshold={J}")
    print(f"Pinned k={k},d={d},n={n}: N={N}, h={h}, rows={m}; T0 row-list size={L0}")
    print(f"Endpoint: every row has the same {s}-element list; Hall deficit={m-s}")
    print(f"Column cost histogram={expected}; all nonzero-cost columns are accessible to m/2 rows")


def cap_value(m, ns, T):
    """Exact symmetry-reduced entropy formula, evaluated in floating arithmetic."""
    logs_a = [log(m)] + [log(m / 2)] * (len(ns) - 1)

    def loads(z):
        return [exp(min(0.0, z + logs_a[j] - j * T)) for j in range(len(ns))]

    lo, hi = -log(m) - 100.0, (len(ns) - 1) * T + 100.0
    for _ in range(120):
        mid = (lo + hi) / 2
        mass = sum(count * gam for count, gam in zip(ns, loads(mid)))
        if mass < m:
            lo = mid
        else:
            hi = mid
    z = (lo + hi) / 2
    gammas = loads(z)
    assert abs(sum(c * g for c, g in zip(ns, gammas)) / m - 1) < 1e-10
    # Dual value: sum column prices plus m log(row partition).
    F = -m * z + sum(ns[j] * max(0.0, z + logs_a[j] - j * T) for j in range(len(ns)))
    free = m * log(ns[0] + sum(ns[j] * exp(-j * T) / 2 for j in range(1, len(ns))))
    assert F <= free + 1e-8
    return F, free


def asymptotic_and_entropy_audit():
    m, s, ns, L0, cheapest, _ = histogram(2)
    F0, _ = cap_value(m, ns, 0.0)
    assert abs(F0 - m * log(L0)) < 1e-8
    print("Sector entropy at k=2: T, F_cap, F_free, capacity gap")
    for T in [0, 1, 4, 16, 64, 256]:
        F, free = cap_value(m, ns, T)
        print(f"  {T:3d} {F:12.5f} {free:12.5f} {free-F:12.5f}")
    F256, _ = cap_value(m, ns, 256)
    F128, _ = cap_value(m, ns, 128)
    assert abs((F128 - F256) / 128 - cheapest) < 1e-8
    print("Asymptotic family: k; upper bound on (k+1)Delta; log-surplus margin/b; min_cost/(r*m)")
    for k in [2, 4, 8, 16, 32, 64, 128]:
        d, n, b, r = 4*k, 5*k+2, 1 << k, 3*k
        N = 1 << n
        eps_bound = log1p(4 * 2.0 ** (-3*k)) / (k+1) - (k+1) * log1p(-2.0**(-n))
        # Lower bound on log(N^b t_k q^r) minus log(h^2 exp(kb/10)), divided by b.
        margin = (1.5*k + 2)*log(2) + 3.5*k*log1p(-2.0**(-n)) - 8*k*log(2)/b - k/10
        assert margin > 0
        assert (N - 1) * 32 >= 30 * N  # p=(N-1)/(2N) >= 15/32
        # K>=64: alpha strictly exceeds uniform unordered edge flux 1/|E|.
        assert 2 * 64 * (N - 1) > 4 * N
        mm, ss, counts, LL, cost, JJ = histogram(k)
        assert ss < mm and LL >= mm
        assert cost <= r * mm / 2
        print(f"  {k:3d} {eps_bound:.4e} {margin:.6f} {cost/(r*mm):.8f}")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert digest == SPEC_SHA
    small_cube_audit()
    rank_finner_audit()
    exact_pinned_audit()
    asymptotic_and_entropy_audit()
    print("Spec.lean SHA-256 unchanged:", digest)
    print("PASS: diagnostic identities only; summed EL remains unproved and unrefuted.")


if __name__ == "__main__":
    main()
