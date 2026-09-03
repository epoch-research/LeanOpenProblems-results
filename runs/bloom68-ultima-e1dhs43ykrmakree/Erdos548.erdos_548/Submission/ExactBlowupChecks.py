"""Exact finite audits for the structural lemmas in ExactBlowupFindings.md.

These checks are not a proof of unrestricted Erdos--Sos.  No Lean file is
changed.  Run: python3 Submission/ExactBlowupChecks.py
"""
from itertools import product, permutations, combinations
import random

import networkx as nx


COUNTS = {}


def weighted_data(F, w):
    n = sum(w.values())
    e = sum(w[i] * w[j] for i, j in F.edges())
    deg = {i: sum(w[j] for j in F[i]) for i in F}
    return n, e, deg


def check_degree_two_bicliques():
    instances = tests = 0
    for size in range(2, 9):
        bound = 6 if size <= 6 else (4 if size == 7 else 3)
        bases = [nx.path_graph(size)]
        if size >= 3:
            bases.append(nx.cycle_graph(size))
        for F in bases:
            for ws in product(range(1, bound + 1), repeat=size):
                w = dict(enumerate(ws))
                n, e, deg = weighted_data(F, w)
                k = (2 * e + n - 1) // n  # largest integer with avg > k-1
                assert 2 * e > (k - 1) * n
                for a in range(1, (k + 1) // 2 + 1):
                    b = k + 1 - a
                    witnesses = [i for i in F if
                                 (w[i] >= a and deg[i] >= b) or
                                 (w[i] >= b and deg[i] >= a)]
                    assert witnesses, (F.edges(), w, k, a, b)
                    tests += 1
                instances += 1
    COUNTS['degree_two_weighted_hosts'] = instances
    COUNTS['degree_two_biclique_certificates'] = tests
    print('Degree-two quotient theorem:', instances, 'hosts;', tests,
          'exact biclique-capacity certificates.')


def check_local_charging():
    count = 0
    # A light quotient class has weight x <= s, and at most two neighbors.
    # Zero represents an absent neighbor.  Check the proof's exact inequality.
    for s in range(1, 9):
        for t in range(s, 17):
            for x in range(1, s + 1):
                for y in range(t + 1):
                    for z in range(t + 1):
                        medium_mass = (y if y > s else 0) + (z if z > s else 0)
                        assert 2 * x * (y + z - s - t) <= s * medium_mass
                        count += 1
    COUNTS['local_charging_inequalities'] = count
    print('Exact local charging inequalities:', count)


def check_criticality_compression():
    tests = 0
    for F0 in nx.graph_atlas_g():
        if not 1 <= len(F0) <= 4:
            continue
        F = nx.convert_node_labels_to_integers(F0)
        m = len(F)
        for ws in product(range(1, 4), repeat=m):
            w = dict(enumerate(ws))
            n, e, deg = weighted_data(F, w)
            if not e:
                continue
            all_counts = list(product(*(range(x + 1) for x in ws)))
            subset_values = [(sum(xs), sum(xs[i] * xs[j] for i, j in F.edges()))
                             for xs in all_counts if tuple(xs) != ws]
            for c in range((2 * e + n - 1) // n):  # c = 2a, positive surplus
                eta2 = 2 * e - c * n
                assert eta2 > 0
                direct = all(2 * es <= c * ns for ns, es in subset_values)
                corners = True
                for mask in range((1 << m) - 1):
                    ns = sum(w[i] for i in F if mask >> i & 1)
                    es = sum(w[i] * w[j] for i, j in F.edges()
                             if mask >> i & 1 and mask >> j & 1)
                    if 2 * es > c * ns:
                        corners = False
                        break
                criterion = corners and all(2 * deg[i] >= c + eta2 for i in F)
                assert direct == criterion, (F.edges(), w, c, direct, criterion)
                tests += 1
    COUNTS['compressed_criticality_equivalences'] = tests
    print('Full-subset versus compressed criticality checks:', tests)


def blowup(F, w):
    H = nx.Graph()
    clusters = {}
    colors = {}
    cursor = 0
    for i in F:
        clusters[i] = list(range(cursor, cursor + w[i]))
        for x in clusters[i]:
            colors[x] = i
        H.add_nodes_from(clusters[i])
        cursor += w[i]
    for i, j in F.edges():
        H.add_edges_from((x, y) for x in clusters[i] for y in clusters[j])
    return H, clusters, colors


def fix_by_swaps(T, h, clusters, missing, phi, cover):
    """Constructive proof: each same-cluster swap strictly reduces conflicts."""
    phi = dict(phi)
    inv = {x: u for u, x in phi.items()}
    assert len(inv) == len(phi) == len(T)
    assert all(phi[u] in clusters[h[u]] for u in T)
    D = max((len(missing[x]) for xs in clusters.values() for x in xs), default=0)
    Delta = max(dict(T.degree()).values(), default=0)
    assert all(len(clusters[i]) >= 2 * Delta * D for i in cover)
    all_edges = list(T.edges())
    conflicts = lambda: [(u, v) for u, v in all_edges if phi[v] in missing[phi[u]]]
    bad = conflicts()
    initial = len(bad)
    steps = 0
    while bad:
        u, v = bad[0]
        if h[u] not in cover:
            u, v = v, u
        assert h[u] in cover
        i = h[u]
        x = phi[u]
        # These are exactly the two forbidden candidate sets in the proof.
        A = {y for y in clusters[i]
             if any(phi[z] in missing[y] for z in T[u])}
        B = {y for y in clusters[i] if y in inv
             and any(phi[z] in missing[x] for z in T[inv[y]])}
        assert x in A & B
        assert len(A) <= Delta * D and len(B) <= Delta * D
        assert len(A | B) <= 2 * Delta * D - 1
        candidates = set(clusters[i]) - A - B
        assert candidates
        y = min(candidates)
        z = inv.get(y)
        assert z != u and (z is None or not T.has_edge(u, z))
        phi[u] = y
        inv[y] = u
        if z is None:
            del inv[x]
        else:
            phi[z] = x
            inv[x] = z
        new_bad = conflicts()
        assert len(new_bad) < len(bad)
        bad = new_bad
        steps += 1
    assert len(set(phi.values())) == len(T)
    assert all(phi[u] in clusters[h[u]] for u in T)
    assert all(phi[v] not in missing[phi[u]] for u, v in T.edges())
    assert steps <= initial
    return phi, steps, initial


def all_bipartite_matchings(left, right):
    # Enumerates each matching exactly once, including the empty matching.
    if not left:
        yield []
        return
    x, *rest = left
    yield from all_bipartite_matchings(rest, right)
    for y in right:
        for M in all_bipartite_matchings(rest, [z for z in right if z != y]):
            yield [(x, y)] + M


def check_spanning_lifts():
    F = nx.path_graph(2)
    H, clusters, colors = blowup(F, {0: 4, 1: 4})
    T = nx.path_graph(8)
    h = {u: u % 2 for u in T}
    even, odd = list(range(0, 8, 2)), list(range(1, 8, 2))
    cases = defects = repaired = steps = 0
    # All matchings deleted from K4,4, and all color-respecting bijections of P8.
    for M in all_bipartite_matchings(clusters[0], clusters[1]):
        missing = {x: set() for x in H}
        for x, y in M:
            missing[x].add(y)
            missing[y].add(x)
        G = H.copy()
        G.remove_edges_from(M)
        # Independent non-induced containment check for every missing matching.
        assert nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_is_monomorphic()
        for lp in permutations(clusters[0]):
            for rp in permutations(clusters[1]):
                phi = dict(zip(even, lp)) | dict(zip(odd, rp))
                out, ns, before = fix_by_swaps(T, h, clusters, missing, phi, {0})
                assert all(G.has_edge(out[u], out[v]) for u, v in T.edges())
                cases += 1
                repaired += bool(before)
                steps += ns
        defects += 1
    COUNTS['spanning_lifts'] = cases
    COUNTS['spanning_defect_graphs'] = defects
    COUNTS['spanning_initially_conflicted'] = repaired
    COUNTS['spanning_repair_swaps'] = steps
    print('Zero-spare-capacity P8 lifts:', cases, 'initial bijections on', defects,
          'defect matchings;', repaired, 'initially conflicted;', steps, 'swaps.')


def check_random_colored_lifts():
    R = random.Random(5842043)
    count = repaired = steps = tight = 0
    for trial in range(1500):
        m = R.randint(2, 6)
        F = nx.random_tree(m, seed=R)
        for i, j in list(nx.non_edges(F)):
            if R.random() < .3:
                F.add_edge(i, j)
        order = R.randint(2, 19)
        T = nx.random_tree(order, seed=R)
        h = {0: R.choice(list(F))}
        for u, v in nx.bfs_edges(T, 0):
            h[v] = R.choice(list(F[h[u]]))
        Delta = max(dict(T.degree()).values())
        d = R.randint(1, 3)
        # Only these quotient edges will have defects; their cover can be small.
        defect_base_edges = [e for e in F.edges() if R.random() < .5]
        if not defect_base_edges:
            defect_base_edges = [R.choice(list(F.edges()))]
        cover = {R.choice(e) for e in defect_base_edges}
        loads = {i: sum(h[u] == i for u in T) for i in F}
        w = {i: max(1, loads[i], 2 * Delta * d if i in cover else 0) for i in F}
        H, clusters, colors = blowup(F, w)
        phi = {}
        for i in F:
            us = [u for u in T if h[u] == i]
            for u, x in zip(us, R.sample(clusters[i], len(us))):
                phi[u] = x
        missing = {x: set() for x in H}
        candidates = [(x, y) for i, j in defect_base_edges
                      for x in clusters[i] for y in clusters[j]]
        R.shuffle(candidates)
        for x, y in candidates:
            if len(missing[x]) < d and len(missing[y]) < d and R.random() < .6:
                missing[x].add(y)
                missing[y].add(x)
        out, ns, before = fix_by_swaps(T, h, clusters, missing, phi, cover)
        assert all(H.has_edge(out[u], out[v]) and out[v] not in missing[out[u]]
                   for u, v in T.edges())
        count += 1
        repaired += bool(before)
        steps += ns
        tight += any(w[i] == 2 * Delta * d for i in cover)
    COUNTS['random_colored_lifts'] = count
    COUNTS['random_initially_conflicted'] = repaired
    COUNTS['random_repair_swaps'] = steps
    COUNTS['random_threshold_equality_cases'] = tight
    print('General colored lifts:', count, '; initially conflicted:', repaired,
          '; swaps:', steps, '; capacity-threshold equality:', tight)


def hall_lift(P, A, B, X, Y, missing, psi):
    """Keep B fixed and match A into common-neighbor lists in X."""
    da = max((P.degree[u] for u in A), default=0)
    db = max((P.degree[v] for v in B), default=0)
    d = max((len(missing[x]) for x in X + Y), default=0)
    assert len(X) >= len(A) and len(Y) >= len(B)
    assert len(X) >= d * (da + db)
    lists = {u: {x for x in X if all(psi[v] not in missing[x] for v in P[u])}
             for u in A}
    assert all(len(X) - len(lists[u]) <= d * da for u in A)
    assert all(sum(x not in lists[u] for u in A) <= d * db for x in X)
    J = nx.Graph()
    left = [('P', u) for u in A]
    J.add_nodes_from(left, bipartite=0)
    J.add_nodes_from([('H', x) for x in X], bipartite=1)
    J.add_edges_from((('P', u), ('H', x)) for u in A for x in lists[u])
    matching = nx.algorithms.bipartite.maximum_matching(J, top_nodes=left)
    assert all(u in matching for u in left)
    phi = dict(psi)
    phi.update({u: matching[('P', u)][1] for u in A})
    assert len(set(phi.values())) == len(P)
    assert all(phi[v] not in missing[phi[u]] for u, v in P.edges())
    return phi


def check_asymmetric_hall_lifts():
    R = random.Random(59280453)
    count = exact = better = 0
    for trial in range(2000):
        P = nx.random_tree(R.randint(2, 27), seed=R)
        colors = nx.bipartite.color(P)
        A = [u for u in P if colors[u] == 0]
        B = [u for u in P if colors[u] == 1]
        if len(A) > len(B):
            A, B = B, A
        da = max(P.degree[u] for u in A)
        db = max(P.degree[v] for v in B)
        d = R.randint(1, 3)
        p = max(len(A), d * (da + db))
        X = list(range(p))
        Y = list(range(p, p + len(B)))
        missing = {x: set() for x in X + Y}
        candidates = [(x, y) for x in X for y in Y]
        R.shuffle(candidates)
        for x, y in candidates:
            if len(missing[x]) < d and len(missing[y]) < d and R.random() < .6:
                missing[x].add(y)
                missing[y].add(x)
        psi = dict(zip(B, R.sample(Y, len(B))))
        out = hall_lift(P, A, B, X, Y, missing, psi)
        assert all(out[u] in X for u in A) and all(out[v] in Y for v in B)
        count += 1
        actual_d = max(map(len, missing.values()))
        exact += p == actual_d * (da + db)
        better += p < 2 * max(da, db) * actual_d
    # A full-capacity example strictly beyond the uniform 2*Delta*d bound.
    P = nx.Graph()
    A = list(range(6))
    next_vertex = 6
    for u in range(5):
        P.add_edges_from([(u, next_vertex), (next_vertex, u + 1)])
        next_vertex += 1
    for u, leaves in enumerate([3, 1, 1, 1, 1, 3]):
        for _ in range(leaves):
            P.add_edge(u, next_vertex)
            next_vertex += 1
    B = list(range(6, 21))
    X, Y = A[:], B[:]
    assert len(P) == 21 and P.number_of_edges() == 20 and nx.is_tree(P)
    assert max(P.degree[u] for u in A) == 4
    assert max(P.degree[v] for v in B) == 2
    for _ in range(500):
        missing = {x: set() for x in X + Y}
        for x, y in zip(X, R.sample(Y, len(X))):
            missing[x].add(y)
            missing[y].add(x)
        psi = dict(zip(B, R.sample(Y, len(B))))
        out = hall_lift(P, A, B, X, Y, missing, psi)
        assert set(out.values()) == set(X + Y)
    COUNTS['asymmetric_hall_lifts'] = count
    COUNTS['asymmetric_hall_threshold_equality'] = exact
    COUNTS['asymmetric_hall_beyond_uniform_bound'] = better
    COUNTS['asymmetric_full_capacity_lifts'] = 500
    print('Asymmetric Hall lifts:', count, '; threshold equality:', exact,
          '; beyond uniform bound:', better, '; extra full-capacity K6,15 cases: 500.')


def critical_near_cycle(t):
    F = nx.cycle_graph(5)
    w = {i: (12 * t if i == 4 else 6 * t) for i in F}
    H, clusters, colors = blowup(F, w)
    q = 6 * t
    M = list(zip(clusters[1], clusters[2]))
    M += list(zip(clusters[3], clusters[4][:q]))
    M += list(zip(clusters[0], clusters[4][q:]))
    assert len(M) == 18 * t and len(set(sum(([x, y] for x, y in M), []))) == len(H)
    removed = M[:-1]
    G = H.copy()
    G.remove_edges_from(removed)
    return F, w, H, G, clusters, colors, removed


def check_critical_family():
    subset_size_bounds = 0
    for t in range(1, 101):
        n = 36 * t
        k = 14 * t
        delta = 12 * t - 1
        a2 = k - 1
        m = 252 * t * t - 18 * t + 1
        assert 2 * m - a2 * n == 2
        for s in range(n):
            if s <= 28 * t - 2:
                assert s * s <= 2 * a2 * s  # Mantel: e(S) <= s^2/4 <= a*s
            else:
                x = n - s
                assert 1 <= x <= 8 * t + 1
                # 4*(I(X)-a|X|) >= (4delta-2a2)x-x^2 > 4.
                assert (4 * delta - 2 * a2) * x - x * x > 4
            subset_size_bounds += 1
    graph_audits = 0
    for t in range(1, 11):
        F, w, H, G, clusters, colors, removed = critical_near_cycle(t)
        n, m = len(G), G.number_of_edges()
        assert n == 36 * t and m == 252 * t * t - 18 * t + 1
        assert min(dict(G.degree()).values()) == 12 * t - 1
        assert max(dict(G.degree()).values()) == 18 * t  # unmatched endpoint in C0
        assert max(dict(nx.Graph(removed).degree()).values()) == 1
        assert sum(nx.triangles(G).values()) == 0
        assert not nx.is_bipartite(G)
        assert len(set(frozenset(G[x]) for x in G)) == n  # no false twins
        assert min(w.values()) == 2 * (3 * t)
        graph_audits += 1
    COUNTS['critical_family_subset_size_bounds'] = subset_size_bounds
    COUNTS['critical_family_explicit_graph_audits'] = graph_audits
    print('Critical approximate-C5 family:', subset_size_bounds,
          'all-subset-size bounds (t=1..100);', graph_audits,
          'explicit nonbipartite, false-twin-free graph audits.')


def check_family_tree_embeddings():
    F, w, H, G, clusters, colors, removed = critical_near_cycle(1)
    missing = {x: set() for x in H}
    for x, y in removed:
        missing[x].add(y)
        missing[y].add(x)
    tests = repairs = 0
    n, e, deg = weighted_data(F, w)
    for T in nx.nonisomorphic_trees(15):
        if max(dict(T.degree()).values()) > 3:
            continue
        color = nx.bipartite.color(T)
        A = [u for u in T if color[u] == 0]
        B = [u for u in T if color[u] == 1]
        if len(A) > len(B):
            A, B = B, A
        a, b = len(A), len(B)
        i = next(i for i in F if
                 (w[i] >= a and deg[i] >= b) or (w[i] >= b and deg[i] >= a))
        if not (w[i] >= a and deg[i] >= b):
            A, B = B, A
        outer = [x for j in F[i] for x in clusters[j]]
        phi = dict(zip(A, clusters[i])) | dict(zip(B, outer))
        h = {u: colors[phi[u]] for u in T}
        out, ns, before = fix_by_swaps(T, h, clusters, missing, phi, set(F))
        assert len(set(out.values())) == 15
        assert all(G.has_edge(out[u], out[v]) for u, v in T.edges())
        tests += 1
        repairs += bool(before)
    COUNTS['critical_family_subcubic_tree_types'] = tests
    COUNTS['critical_family_tree_types_repaired'] = repairs
    print('Critical k=14 host:', tests, 'nonisomorphic subcubic tree types embedded;',
          repairs, 'completion copies required repair.')


def check_nonmodular_critical_family():
    qs = [q for q in range(5, 150, 4)
          if all(q % p for p in range(2, int(q ** .5) + 1))]
    subsets = 0
    for q in qs:
        r = (q - 1) // 4
        squares = {x * x % q for x in range(1, q)}
        H = nx.Graph()
        H.add_nodes_from(range(q))
        H.add_edges_from((x, y) for x in range(q) for y in range(x + 1, q)
                         if (x - y) % q in squares)
        assert nx.is_connected(H) and all(H.degree[x] == 2 * r for x in H)
        for x, y in combinations(H, 2):
            assert len(set(H[x]) & set(H[y])) == (r - 1 if H.has_edge(x, y) else r)
        G = H.copy()
        G.add_edge(*next(iter(nx.non_edges(H))))
        assert G.number_of_edges() == r * q + 1
        assert all(len(set(G[x]) ^ set(G[y])) >= 2 * r - 2
                   for x, y in combinations(G, 2))
        if q <= 17:
            bits = [sum(1 << v for v in G[u]) for u in G]
            es = [0] * (1 << q)
            for mask in range(1, (1 << q) - 1):
                bit = mask & -mask
                u = bit.bit_length() - 1
                rest = mask ^ bit
                es[mask] = es[rest] + (bits[u] & rest).bit_count()
                assert es[mask] <= r * mask.bit_count()
                subsets += 1
    COUNTS['nonmodular_critical_hosts'] = len(qs)
    COUNTS['nonmodular_critical_direct_subsets'] = subsets
    print('Paley-plus-edge:', len(qs), 'critical host audits;', subsets,
          'direct proper-subset checks through order 17.')


def main():
    check_degree_two_bicliques()
    check_local_charging()
    check_criticality_compression()
    check_spanning_lifts()
    check_random_colored_lifts()
    check_asymmetric_hall_lifts()
    check_critical_family()
    check_family_tree_embeddings()
    check_nonmodular_critical_family()
    print('ALL CHECKS PASSED')
    print(COUNTS)


if __name__ == '__main__':
    main()
