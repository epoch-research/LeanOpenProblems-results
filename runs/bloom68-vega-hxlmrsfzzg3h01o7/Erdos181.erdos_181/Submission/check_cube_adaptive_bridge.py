#!/usr/bin/env python3
"""Finite audits for CubeAdaptiveBridgeAttempt.md.

The paper proofs, not these small instances, establish the identities.
This script does NOT test or assume the missing robust-core-to-cube implication.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb
from pathlib import Path
from random import Random
import hashlib

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

ROOT = Path(__file__).resolve().parent
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def submasks(mask):
    s = mask
    while True:
        yield s
        if not s:
            return
        s = (s - 1) & mask


def vertices(mask):
    return [i for i in range(mask.bit_length()) if (mask >> i) & 1]


def graph_from_mask(n, mask):
    adj = [0] * n
    for i, (u, v) in enumerate(combinations(range(n), 2)):
        if (mask >> i) & 1:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return adj


def complement(adj):
    full = (1 << len(adj)) - 1
    return [full ^ (1 << u) ^ row for u, row in enumerate(adj)]


def cube_edges(k):
    return [(x, x ^ (1 << i)) for x in range(1 << k)
            for i in range(k) if not (x >> i) & 1]


def block_embeddings(adj, k):
    return [g for g in permutations(range(len(adj)), 1 << k)
            if all((adj[g[x]] >> g[y]) & 1 for x, y in cube_edges(k))]


def image(g):
    return sum(1 << v for v in g)


def compatible(adj, t, x, g, y, h):
    if x == y or image(g) & image(h):
        return False
    return ((x ^ y).bit_count() != 1
            or all((adj[u] >> v) & 1 for u, v in zip(g, h)))


def all_packings(adj, k, t):
    embeddings = block_embeddings(adj, k)
    q = 1 << t
    result = []
    current = []

    def visit(x):
        if x == q:
            result.append(tuple(current))
            return
        current.append(None)
        visit(x + 1)
        current.pop()
        for g in embeddings:
            if all(h is None or compatible(adj, t, x, g, y, h)
                   for y, h in enumerate(current)):
                current.append(g)
                visit(x + 1)
                current.pop()
    visit(0)
    return result


def state_data(p):
    dom, used = 0, 0
    for x, g in enumerate(p):
        if g is not None:
            dom |= 1 << x
            assert not used & image(g)
            used |= image(g)
    return dom, used


def check_global_rebuilds():
    # Every colouring of K_5, both colours, and two genuine blockings of Q_2.
    hosts = batches = equalities = deficient = 0
    n = 5
    rows = [1 << v for v in range(n)] + [0b00111, 0b11100]
    weights = [1, 2, 3, 1, 2, 3, 2]

    def penalty(used):
        return sum(w * (1 << (used & s).bit_count())
                   for w, s in zip(weights, rows))

    for mask in range(1 << comb(n, 2)):
        red = graph_from_mask(n, mask)
        for adj in (red, complement(red)):
            for k, t in ((0, 2), (1, 1)):
                states = all_packings(adj, k, t)
                data = {p: state_data(p) for p in states}
                p = max(states, key=lambda u: (
                    data[u][0].bit_count(), -penalty(data[u][1])))
                pdom, pused = data[p]
                maximum = pdom.bit_count()
                deficient += maximum < (1 << t)
                hosts += 1
                for batch in states:
                    bdom, bused = data[batch]
                    removed = 0
                    for x, g in enumerate(p):
                        if g is not None and any(
                            h is not None and not compatible(adj, t, x, g, y, h)
                            for y, h in enumerate(batch)):
                            removed |= 1 << x
                    rebuilt = tuple(batch[x] if batch[x] is not None
                                    else (None if (removed >> x) & 1 else p[x])
                                    for x in range(1 << t))
                    assert rebuilt in data  # independent enumeration of all states
                    assert bdom.bit_count() <= removed.bit_count()
                    rused = 0
                    for x in vertices(removed):
                        rused |= image(p[x])
                    newdom, newused = data[rebuilt]
                    assert newdom.bit_count() == maximum - removed.bit_count() + bdom.bit_count()
                    assert newused == (pused & ~rused) | bused
                    if bdom.bit_count() == removed.bit_count():
                        equalities += 1
                        assert penalty(newused) >= penalty(pused)
                        # Exact exponential exchange invariant, without floating point.
                        delta = sum(w * ((1 << ((pused & s).bit_count()
                                                    - (rused & s).bit_count()
                                                    + (bused & s).bit_count()))
                                         - (1 << (pused & s).bit_count()))
                                    for w, s in zip(weights, rows))
                        assert delta == penalty(newused) - penalty(pused) >= 0
                    boundary = 0
                    for x in vertices(bdom):
                        for i in range(t):
                            boundary |= 1 << (x ^ (1 << i))
                    boundary &= ~bdom
                    outside_hits = sum(
                        bool(image(g) & bused)
                        for x, g in enumerate(p)
                        if g is not None and not ((bdom | boundary) >> x) & 1)
                    assert (bdom & ~pdom).bit_count() <= (
                        (pdom & boundary).bit_count() + outside_hits)
                    batches += 1
    print(f"Global rebuilds: {hosts} fully optimized coloured/blocking instances; "
          f"{batches} arbitrary batches; {equalities} equal-size potential inequalities; "
          f"{deficient} deficient optima")


def cut_cost(adj, degree_cap, a, z):
    outside = ((1 << len(adj)) - 1) & ~(a | z)
    h = sum((adj[v] & outside).bit_count() > degree_cap for v in vertices(a))
    return h + z.bit_count()


def weighted_cut_cost(adj, degree_cap, a, z):
    result = sum(zv - av for av, zv in zip(a, z))
    for v, av in enumerate(a):
        ordered = sorted(z[u] for u in vertices(adj[v]))
        if len(ordered) > degree_cap:
            result += max(0, av - ordered[degree_cap])
    return result


def check_coarea():
    rng = Random(1810601)
    n = 5
    full = (1 << n) - 1
    minima = potentials = rounded = 0
    for mask in range(1 << comb(n, 2)):
        red = graph_from_mask(n, mask)
        for adj in (red, complement(red)):
            for cap in (0, 1):
                cuts = [(Fraction(cut_cost(adj, cap, a, z), a.bit_count()), a, z)
                        for a in range(1, 1 << n) if a.bit_count() <= n // 2
                        for z in submasks(full ^ a)]
                minimum, best_a, best_z = min(cuts)
                # Binary potentials attain the exact cut minimum.
                av = [int((best_a >> v) & 1) for v in range(n)]
                zv = [int(((best_a | best_z) >> v) & 1) for v in range(n)]
                assert Fraction(weighted_cut_cost(adj, cap, av, zv), sum(av)) == minimum
                minima += 1
                for _ in range(12):
                    support = rng.sample(range(n), rng.randrange(1, n // 2 + 1))
                    av = [0] * n
                    for v in support:
                        av[v] = rng.randrange(1, 5)
                    zv = [a + rng.randrange(4) for a in av]
                    lhs = weighted_cut_cost(adj, cap, av, zv)
                    integrated = 0
                    witnesses = []
                    for s in range(max(zv)):
                        a = sum(1 << v for v in range(n) if av[v] > s)
                        z = sum(1 << v for v in range(n) if av[v] <= s < zv[v])
                        value = cut_cost(adj, cap, a, z)
                        integrated += value
                        if a and 8 * value <= a.bit_count():
                            witnesses.append((a, z))
                    assert lhs == integrated
                    assert Fraction(lhs, sum(av)) >= minimum
                    if 8 * lhs <= sum(av):
                        assert witnesses
                        rounded += 1
                    potentials += 1
    # A genuinely globally deficient small core, not a failed chosen boundary.
    cycle = [0] * 5
    for v in range(5):
        cycle[v] = (1 << ((v - 1) % 5)) | (1 << ((v + 1) % 5))
    for adj in (cycle, complement(cycle)):
        assert all(8 * cut_cost(adj, 0, a, z) > a.bit_count()
                   for a in range(1, 32) if a.bit_count() <= 2
                   for z in submasks(31 ^ a))
        assert max(state_data(p)[0].bit_count() for p in all_packings(adj, 0, 2)) == 3
    print(f"Coarea: {minima} exhaustive cut minima; {potentials} multilevel potential identities; "
          f"{rounded} literal threshold witnesses; both-colour C_5 core audited")


def check_local_moment_duality():
    # Actual labelled Q_1's in arbitrary 3-by-3 partite graphs.
    query_sets = [0b001001, 0b010010, 0b100100, 0b011101, 0b110011, 0b101110]
    beta = [Fraction(3 + (s & 7).bit_count(), 3)
            * Fraction(3 + (s >> 3).bit_count(), 3) for s in query_sets]
    cases = feasible = separated = 0
    for mask in range(1, 1 << 9):
        actual = [(u, v + 3) for u in range(3) for v in range(3)
                  if (mask >> (3 * u + v)) & 1]
        exact = [[Fraction(1 << (image(g) & s).bit_count()) - bound
                  for g in actual] for s, bound in zip(query_sets, beta)]
        a = np.array(exact, dtype=float)
        r, q = a.shape
        primal = linprog(np.r_[np.zeros(q), 1.0],
                         A_ub=np.c_[a, -np.ones(r)], b_ub=np.zeros(r),
                         A_eq=np.array([np.r_[np.ones(q), 0.0]]), b_eq=[1.0],
                         bounds=[(0, None)] * q + [(None, None)], method="highs")
        dual = linprog(np.r_[np.zeros(r), -1.0],
                       A_ub=np.c_[-a.T, np.ones(q)], b_ub=np.zeros(q),
                       A_eq=np.array([np.r_[np.ones(r), 0.0]]), b_eq=[1.0],
                       bounds=[(0, None)] * r + [(None, None)], method="highs")
        assert primal.success and dual.success
        assert abs(primal.fun + dual.fun) < 1e-8
        mu = [Fraction(float(v)).limit_denominator(1000000) for v in primal.x[:q]]
        lam = [Fraction(float(v)).limit_denominator(1000000) for v in dual.x[:r]]
        assert sum(mu) == sum(lam) == 1 and min(mu + lam) >= 0
        upper = max(sum(row[j] * mu[j] for j in range(q)) for row in exact)
        lower = min(sum(lam[i] * exact[i][j] for i in range(r)) for j in range(q))
        assert upper == lower  # exact rational saddle point, not only solver status
        if upper <= 0:
            feasible += 1
        else:
            assert all(sum(lam[i] * exact[i][j] for i in range(r)) > 0 for j in range(q))
            separated += 1
        cases += 1
    # Unconditional mixing of boundaries loses the conditional constraints.
    excess = ((Fraction(3, 2), Fraction(-3, 2)),
              (Fraction(-3, 2), Fraction(3, 2)))
    assert all(max(row) > 0 for row in excess)
    assert [sum(row[i] for row in excess) / 2 for i in range(2)] == [0, 0]
    for j in range(101):
        lam = [Fraction(j, 100), Fraction(100 - j, 100)]
        assert min(sum(x * y for x, y in zip(lam, row)) for row in excess) <= 0
    print(f"Moment minimax: {cases} actual-block games, with exact rational saddle points; "
          f"{feasible} feasible and {separated} strictly separated; boundary-mixture trap checked")


def sparse_matrix(entries, shape):
    if not entries:
        return coo_matrix(shape).tocsr()
    r, c, v = zip(*entries)
    return coo_matrix((v, (r, c)), shape=shape).tocsr()


def history_forest(adj, roots_data):
    """Finite actual-block capacity histories; every job is a labelled Q_1.

    L=4; theta=log 2; use the rational stronger budget (3/2)^overlap,
    which is <= exp(overlap/2). Roots may have different list systems.
    These are tests of the general flow/dual lemma, not a robust-core model.
    """
    nodes, edges, roots = [], [], []
    for jobs in roots_data:
        original_rows = [s for job in jobs for s in job]
        memo = {}

        def visit(j, used):
            key = j, used
            if key in memo:
                return memo[key]
            idx = len(nodes)
            memo[key] = idx
            if j == len(jobs):
                nodes.append((True, "success", len(original_rows)))
                return idx
            available = [s & ~used for s in jobs[j]]
            if any(s.bit_count() < 2 for s in available):
                nodes.append((True, "stopped", len(original_rows)))
                return idx
            nodes.append((False, "internal", len(original_rows)))
            beta = [Fraction(3, 2) ** sum((s & row).bit_count() for s in jobs[j])
                    for row in original_rows]
            for u in vertices(available[0]):
                for v in vertices(available[1]):
                    if u == v or not ((adj[u] >> v) & 1):
                        continue
                    hit = (1 << u) | (1 << v)
                    child = visit(j + 1, used | hit)
                    a = [Fraction(1 << (hit & row).bit_count()) - b
                         for row, b in zip(original_rows, beta)]
                    edges.append((idx, child, a))
            return idx
        roots.append(visit(0, 0))
    return nodes, edges, roots


def solve_flow_alternative(nodes, edges, roots):
    internals = [s for s, node in enumerate(nodes) if not node[0]]
    ni = len(internals)
    internal_index = {s: i for i, s in enumerate(internals)}
    nr, ne = len(roots), len(edges)
    mom_index = {}
    for s in internals:
        for r in range(nodes[s][2]):
            mom_index[s, r] = len(mom_index)
    nm = len(mom_index)
    eq, ub = [], []
    for j, root in enumerate(roots):
        assert root in internal_index
        eq.append((internal_index[root], j, -1.0))
        eq.append((ni, j, 1.0))
    for j, (s, child, a) in enumerate(edges):
        eq.append((internal_index[s], nr + j, 1.0))
        if child in internal_index:
            eq.append((internal_index[child], nr + j, -1.0))
        for r, value in enumerate(a):
            ub.append((mom_index[s, r], nr + j, float(value)))
    aeq = sparse_matrix(eq, (ni + 1, nr + ne))
    aub = sparse_matrix(ub, (nm, nr + ne))
    beq = np.r_[np.zeros(ni), 1.0]
    primal = linprog(np.zeros(nr + ne), A_ub=aub, b_ub=np.zeros(nm),
                     A_eq=aeq, b_eq=beq, bounds=(0, None), method="highs")
    dual_rows = []
    for j, (s, child, a) in enumerate(edges):
        dual_rows.append((j, internal_index[s], 1.0))
        if child in internal_index:
            dual_rows.append((j, internal_index[child], -1.0))
        for r, value in enumerate(a):
            dual_rows.append((j, ni + mom_index[s, r], -float(value)))
    for j, root in enumerate(roots):
        dual_rows.append((ne + j, internal_index[root], -1.0))
    adual = sparse_matrix(dual_rows, (ne + nr, ni + nm))
    bdual = np.r_[np.zeros(ne), -np.ones(nr)]
    dual = linprog(np.zeros(ni + nm), A_ub=adual, b_ub=bdual,
                   bounds=[(None, None)] * ni + [(0, None)] * nm, method="highs")
    assert primal.success != dual.success
    assert primal.status in (0, 2) and dual.status in (0, 2)
    if primal.success:
        assert np.max(np.abs(aeq @ primal.x - beq)) < 1e-7
        assert np.max(aub @ primal.x, initial=0) < 1e-7
        assert np.min(primal.x, initial=0) >= -1e-8
    else:
        assert np.max(adual @ dual.x - bdual, initial=0) < 1e-7
        assert np.min(dual.x[ni:], initial=0) >= -1e-8
    return primal.success, len(nodes), len(edges)


def check_global_flow_dual():
    rng = Random(1810602)
    cases = yes = no = nodes_total = edges_total = 0
    n = 12
    # Arbitrary root choices are kept separate; their conditional rows are NOT averaged.
    for density in (0.0, 0.10, 0.25, 0.50, 1.0):
        for _ in range(4):
            adj = [0] * n
            for u, v in combinations(range(n), 2):
                if rng.random() < density:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            roots_data = []
            for _ in range(3):
                jobs = []
                for _ in range(3):
                    parts = rng.sample(range(n), 8)
                    jobs.append((sum(1 << v for v in parts[:4]),
                                 sum(1 << v for v in parts[4:])))
                roots_data.append(jobs)
            nodes, edges, roots = history_forest(adj, roots_data)
            good, nn, ne = solve_flow_alternative(nodes, edges, roots)
            yes += good
            no += not good
            cases += 1
            nodes_total += nn
            edges_total += ne
    assert yes and no
    print(f"Global conditional flow/Farkas alternative: {cases} multi-root instances; "
          f"{yes} feasible, {no} globally separated; "
          f"{nodes_total} history states, {edges_total} actual-block transitions "
          "(LP residuals checked to 1e-7)")


def choose(n, r):
    return comb(n, r) if 0 <= r <= n else 0


def check_balls_and_budgets():
    balls = 0
    for t in range(1, 201):
        r = min(range(1, t + 1, 2), key=lambda r: abs(2 * r - t))
        s = (r - 1) // 2
        z = sum(choose(t, 2 * j) for j in range(s + 1))
        u = sum(choose(t, 2 * j + 1) for j in range(s + 1))
        assert u - z == choose(t - 1, r)
        assert u + z == sum(choose(t, j) for j in range(r + 1))
        assert choose(t, r) ** 2 * (t + 1) <= 2 * (1 << (2 * t))
        assert choose(t, r + 1) ** 2 * (t + 1) <= 2 * (1 << (2 * t))
        if t <= 12:
            ball = {x for x in range(1 << t) if x.bit_count() <= r}
            inner_boundary = {x for x in ball if any(
                (x ^ (1 << i)) not in ball for i in range(t))}
            outer_boundary = {x ^ (1 << i) for x in ball for i in range(t)} - ball
            assert len(inner_boundary) == (choose(t, r) if r < t else 0)
            assert len(outer_boundary) == choose(t, r + 1)
        balls += 1
    # Verify the row-overlap budget without within-block list disjointness.
    rng = Random(1810603)
    overlaps = 0
    for _ in range(1000):
        rows = [sum(1 << v for v in rng.sample(range(20), 6)) for _ in range(12)]
        load = [sum((s >> v) & 1 for s in rows) for v in range(20)]
        rho = max(load)
        for s in rows:
            assert sum((s & other).bit_count() for other in rows) == sum(
                load[v] for v in vertices(s)) <= rho * 6
            overlaps += 1
    print(f"Separator geometry: {balls} central Hamming-ball identities through t=200; "
          f"{overlaps} exact aggregate row-load budgets (overlapping within-block lists allowed)")


def main():
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    check_global_rebuilds()
    check_coarea()
    check_local_moment_duality()
    check_global_flow_dual()
    check_balls_and_budgets()
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    print("PASS: all finite audits; Spec.lean unchanged.")
    print("NOT PROVED: robust core => viable global capacity flow, augmenting rebuild, or low-waste cut.")


if __name__ == "__main__":
    main()
