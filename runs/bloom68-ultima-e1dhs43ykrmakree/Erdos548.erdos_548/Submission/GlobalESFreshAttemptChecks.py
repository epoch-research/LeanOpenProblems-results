"""Exact audits for GlobalESFreshAttempt.md; no Lean imports or edits.

This does not prove unrestricted Erdos--Sos.  It checks the new packing
lemmas, their necessary qualifications, canonical leaf-Hall obstructions,
and the exact covariance/nonneighbor identity.  The mathematical proofs
are in the companion report; finite tests are not their replacements.

Run: python3 Submission/GlobalESFreshAttemptChecks.py
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import math
import random
import time

import networkx as nx

# Read-only use of the previously independently checked subset-polynomial DP.
from DegreeCorrectedMeasureChecks import SquareZeroWeight, rooted_shape, critical

SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"
STATS = Counter()


def lean_hashes():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in Path(__file__).parent.glob("*.lean")}


def root_embedding(F, roots, G, images):
    """Independent injective backtracker with all root images fixed."""
    if len(set(images)) != len(images):
        return None
    image, used = dict(zip(roots, images)), set(images)
    parent, order = {}, []
    for root in roots:
        queue = [root]
        for u in queue:
            for v in F[u]:
                if v == parent.get(u):
                    continue
                parent[v] = u
                queue.append(v)
                order.append(v)
    assert set(order) | set(roots) == set(F)

    def rec(i):
        if i == len(order):
            return dict(image)
        u = order[i]
        for v in G[image[parent[u]]]:
            if v in used or G.degree(v) < F.degree(u):
                continue
            image[u] = v
            used.add(v)
            answer = rec(i + 1)
            if answer is not None:
                return answer
            used.remove(v)
            del image[u]
        return None

    return rec(0)


def verify_embedding(F, G, image):
    assert set(image) == set(F)
    assert len(set(image.values())) == len(F)
    assert all(G.has_edge(image[u], image[v]) for u, v in F.edges())


def forest_from_components(components):
    F, roots = nx.Graph(), []
    for T, root in components:
        offset = len(F)
        labels = {v: offset + i for i, v in enumerate(T)}
        F.add_nodes_from(labels.values())
        F.add_edges_from((labels[u], labels[v]) for u, v in T.edges())
        roots.append(labels[root])
    return F, roots


def small_rooted_forests():
    profiles = []
    for p in (2, 3):
        for es in product(range(1, 5), repeat=p):
            if sum(es) + p > 7 or tuple(sorted(es)) != es:
                continue
            choices = []
            for e in es:
                choices_e = []
                for T in nx.nonisomorphic_trees(e + 1):
                    seen = set()
                    for root in T:
                        shape = rooted_shape(T, root)
                        if shape not in seen:
                            seen.add(shape)
                            choices_e.append((T, root))
                choices.append(choices_e)
            profiles.extend(forest_from_components(c) for c in product(*choices))
    return profiles


def independent_root_audit():
    profiles = small_rooted_forests()
    for G in nx.graph_atlas_g():
        if len(G) < 4:
            continue
        for F, roots in profiles:
            e = F.number_of_edges()
            if len(F) > len(G) or min(dict(G.degree()).values()) < e:
                continue
            for images in permutations(G, len(roots)):
                if any(G.has_edge(u, v) for u, v in combinations(images, 2)):
                    continue
                image = root_embedding(F, roots, G, images)
                assert image is not None
                verify_embedding(F, G, image)
                assert all(image[r] == v for r, v in zip(roots, images))
                STATS["prescribed independent-root embeddings"] += 1
    assert len(profiles) == 31
    assert STATS["prescribed independent-root embeddings"] == 17092

    # Independence cannot simply be dropped: two adjacent prescribed roots.
    G = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
    G.add_edge(2, 3)
    F = nx.Graph([(0, 1), (2, 3)])
    assert min(dict(G.degree()).values()) == 2
    assert root_embedding(F, [0, 2], G, [0, 1]) is None

    # A prescribed isolated root is a genuine exception, even if independent.
    G = nx.cycle_graph(4)
    F = nx.path_graph(3)
    F.add_node(3)
    assert not G.has_edge(0, 2)
    assert root_embedding(F, [0, 3], G, [0, 2]) is None
    STATS["root-theorem boundary counterexamples"] += 2


def slot_matching(demands, neighborhoods):
    """Maximum matching from labelled demand slots, plus a Hall witness.

    Return (slots, left_to_right, deficient_parent_set, neighborhood_set).
    On success the last two sets are empty.  A failure witness is extracted
    by alternating reachability from all unmatched demand slots.
    """
    slots = [(i, j) for i, a in enumerate(demands) for j in range(a)]
    right_match = {}

    def augment(slot, visited):
        i, _ = slots[slot]
        for v in sorted(neighborhoods[i]):
            if v in visited:
                continue
            visited.add(v)
            if v not in right_match or augment(right_match[v], visited):
                right_match[v] = slot
                return True
        return False

    for slot in range(len(slots)):
        augment(slot, set())
    left_match = {slot: v for v, slot in right_match.items()}
    if len(left_match) == len(slots):
        return slots, left_match, set(), set()

    left_seen = set(range(len(slots))) - set(left_match)
    queue = deque(left_seen)
    right_seen = set()
    while queue:
        slot = queue.popleft()
        i, _ = slots[slot]
        for v in neighborhoods[i]:
            if v in right_seen:
                continue
            right_seen.add(v)
            assert v in right_match  # Otherwise this is an augmenting path.
            other = right_match[v]
            if other not in left_seen:
                left_seen.add(other)
                queue.append(other)
    parents = {slots[s][0] for s in left_seen}
    neighborhood = set().union(*(neighborhoods[i] for i in parents))
    assert neighborhood == right_seen
    assert len(neighborhood) < sum(demands[i] for i in parents)
    return slots, left_match, parents, neighborhood


def weighted_hall(demands, lists):
    p = len(demands)
    for bits in range(1, 1 << p):
        indices = [i for i in range(p) if bits & (1 << i)]
        if len(set().union(*(lists[i] for i in indices))) < sum(demands[i] for i in indices):
            return False
    return True


def allocate_reservoirs(demands, lists):
    sizes = [a + 1 for a in demands]
    slots, match, _, _ = slot_matching(sizes, lists)
    assert len(match) == sum(sizes)
    reservoirs = [set() for _ in sizes]
    for slot, v in match.items():
        reservoirs[slots[slot][0]].add(v)
    assert len(set().union(*reservoirs)) == sum(sizes)
    assert all(len(A) == a + 1 and A <= L
               for A, a, L in zip(reservoirs, demands, lists))
    return reservoirs


def star_reservoir_embedding(G, demands, reservoirs):
    """Constructive weighted-Hall star packing; no embedding backtracking.

    The potential is the number of edges amongst the current root images.
    A failed leaf matching explicitly provides a root move decreasing it.
    Only reservoir vertices, not all host vertices, need degree >= e(F).
    """
    p, e = len(demands), sum(demands)
    assert all(a >= 1 for a in demands)
    assert all(len(A) == a + 1 for A, a in zip(reservoirs, demands))
    assert len(set().union(*reservoirs)) == e + p
    assert all(G.degree(v) >= e for v in set().union(*reservoirs))
    roots = [min(A) for A in reservoirs]
    potentials = []
    for _ in range(p * (p - 1) // 2 + 1):
        R = set(roots)
        potential = G.subgraph(R).number_of_edges()
        if potentials:
            assert potential < potentials[-1]
        potentials.append(potential)
        neighborhoods = [set(G[v]) - R for v in roots]
        slots, match, S, Y = slot_matching(demands, neighborhoods)
        if len(match) == e:
            image = {("root", i): v for i, v in enumerate(roots)}
            for slot, v in match.items():
                i, j = slots[slot]
                image[(i, j)] = v
            assert len(set(image.values())) == e + p
            assert all(image[("root", i)] in reservoirs[i] for i in range(p))
            assert all(G.has_edge(image[("root", i)], image[(i, j)])
                       for i, a in enumerate(demands) for j in range(a))
            STATS["star packing root exchanges"] += len(potentials) - 1
            STATS["star packings needing an exchange"] += len(potentials) > 1
            return image, potentials

        eligible = set().union(*(reservoirs[i] for i in S)) - R - Y
        assert eligible
        z = min(eligible)
        i = next(i for i in S if z in reservoirs[i])
        old = roots[i]
        assert all(not G.has_edge(z, roots[j]) for j in S)
        old_inside = len(set(G[old]) & R)
        new_inside = len(set(G[z]) & (R - {old}))
        assert old_inside >= e - sum(demands[j] for j in S) + 1
        assert old_inside >= p - len(S) + 1
        assert new_inside <= p - len(S)
        roots[i] = z
    raise AssertionError("Strictly decreasing nonnegative potential did not terminate")


def disjoint_reservoir_choices(vertices, sizes):
    if not sizes:
        yield []
        return
    for A in combinations(vertices, sizes[0]):
        rest = tuple(v for v in vertices if v not in A)
        for tail in disjoint_reservoir_choices(rest, sizes[1:]):
            yield [set(A)] + tail


def star_hall_audit():
    profiles = []
    for p in (2, 3):
        for demands in product(range(1, 5), repeat=p):
            if tuple(sorted(demands)) == demands and sum(demands) + p <= 7:
                profiles.append(demands)
    for G in nx.graph_atlas_g():
        if len(G) < 4:
            continue
        delta = min(dict(G.degree()).values())
        for demands in profiles:
            e, p = sum(demands), len(demands)
            if delta < e or len(G) < e + p:
                continue
            for reservoirs in disjoint_reservoir_choices(tuple(G), [a + 1 for a in demands]):
                star_reservoir_embedding(G, demands, reservoirs)
                STATS["exhaustive disjoint-reservoir star packings"] += 1

    # Deliberately starts with four roots in a single K5; two global rematches.
    G = nx.disjoint_union(nx.complete_graph(5), nx.complete_graph(5))
    reservoirs = [{0, 5}, {1, 6}, {2, 7}, {3, 8}]
    _, potentials = star_reservoir_embedding(G, [1, 1, 1, 1], reservoirs)
    assert potentials == [6, 3, 2]
    print("  forced exchange potentials:", potentials)

    rng = random.Random(5482026)
    for _ in range(1200):
        p = rng.randrange(2, 7)
        demands = [rng.randrange(1, 5) for _ in range(p)]
        e, total = sum(demands), sum(demands) + p
        n = total + rng.randrange(0, 9)
        G = nx.gnm_random_graph(n, min(n*(n-1)//2, (e + 2)*n//2), seed=rng)
        for v in G:
            while G.degree(v) < e:
                G.add_edge(v, rng.choice(sorted(set(G) - set(G[v]) - {v})))
        lists = [set(rng.sample(range(n), rng.randrange(a + 1, n + 1))) for a in demands]
        ok = weighted_hall([a + 1 for a in demands], lists)
        _, match, _, _ = slot_matching([a + 1 for a in demands], lists)
        assert ok == (len(match) == total)
        STATS["weighted Hall/allocation equivalences"] += 1
        if ok:
            reservoirs = allocate_reservoirs(demands, lists)
            image, _ = star_reservoir_embedding(G, demands, reservoirs)
            assert all(image[("root", i)] in lists[i] for i in range(p))
            STATS["additional different-list star packings"] += 1

    # Minimum degree outside the root candidates is unnecessary.
    demands = [2, 1, 3]
    e, total = sum(demands), sum(demands) + len(demands)
    G = nx.empty_graph(total * (e + 1))
    for center in range(total):
        G.add_edges_from((center, total + center*e + j) for j in range(e))
    reservoirs, offset = [], 0
    for a in demands:
        reservoirs.append(set(range(offset, offset + a + 1)))
        offset += a + 1
    assert min(dict(G.degree()).values()) == 1 < e
    star_reservoir_embedding(G, demands, reservoirs)
    STATS["high-candidate-only star examples"] += 1

    # Weighted Hall alone cannot allow isolated marked components.
    G = nx.path_graph(3)
    F = nx.Graph([(0, 1)])
    F.add_node(2)
    lists = [{0, 2}, {1}]
    assert weighted_hall([2, 1], lists)
    assert all(root_embedding(F, [0, 2], G, [r, 1]) is None for r in lists[0])
    STATS["root-theorem boundary counterexamples"] += 1


def canonical_hall_audit():
    for p in range(1, 4):
        for demands in product((1, 2), repeat=p):
            for q in range(4):
                for masks in product(range(1 << q), repeat=p):
                    neighborhoods = [{j for j in range(q) if mask & (1 << j)} for mask in masks]
                    _, match, reached, _ = slot_matching(demands, neighborhoods)
                    if len(match) != sum(demands) - 1:
                        continue
                    deficient = []
                    for bits in range(1, 1 << p):
                        P = {i for i in range(p) if bits & (1 << i)}
                        nu = len(set().union(*(neighborhoods[i] for i in P)))
                        defect = sum(demands[i] for i in P) - nu
                        assert defect <= 1
                        if defect == 1:
                            deficient.append(P)
                    assert deficient
                    minimum = set.intersection(*deficient)
                    maximum = set.union(*deficient)
                    assert minimum and minimum in deficient and maximum in deficient
                    assert minimum == reached
                    for A in deficient:
                        for B in deficient:
                            assert A & B in deficient and A | B in deficient
                    for i in range(p):
                        smaller = list(demands)
                        smaller[i] -= 1
                        _, matching, _, _ = slot_matching(smaller, neighborhoods)
                        assert (len(matching) == sum(smaller)) == (i in minimum)
                    STATS["canonical deficiency-one Hall systems"] += 1


def split_host(r):
    b = r*r + 1
    G = nx.empty_graph(r + b)
    G.add_edges_from((i, j) for i in range(r) for j in range(i + 1, r + b))
    return G


def subdivide_tree(H):
    T = nx.empty_graph(len(H) + H.number_of_edges())
    midpoint = {}
    for j, (u, v) in enumerate(H.edges()):
        w = len(H) + j
        midpoint[frozenset((u, v))] = w
        T.add_edges_from(((u, w), (v, w)))
    return T, midpoint


def hall_core_family_audit():
    for r in range(2, 21):
        b = r*r + 1
        for x in range(r + 1):
            for y in range(b + 1):
                sigma = x*(x - 2*r) + (2*x - 2*r + 1)*y
                if (x, y) == (r, b):
                    assert sigma == 1
                else:
                    assert sigma <= 0
                STATS["critical split induced-subset types"] += 1
    for r in range(2, 8):
        G = split_host(r)
        A, B = set(range(r)), set(range(r, len(G)))
        for H0 in nx.nonisomorphic_trees(r + 1):
            H = nx.convert_node_labels_to_integers(H0)
            T, mids = subdivide_tree(H)
            leaves = [v for v in T if T.degree(v) == 1]
            core = set(T) - set(leaves)
            I = T.subgraph(core).copy()
            for ell in leaves:
                q = next(iter(H[ell]))
                p = mids[frozenset((ell, q))]
                high_labels = {q} | (set(mids.values()) - {p})
                assert len(high_labels) == r and high_labels <= core
                image = dict(zip(sorted(high_labels), sorted(A)))
                low_labels = [p] + sorted(core - high_labels - {p})
                image.update(zip(low_labels, sorted(B)))
                verify_embedding(I, G, image)
                parent_labels = sorted({next(iter(T[v])) for v in leaves})
                demands = [sum(next(iter(T[v])) == u for v in leaves) for u in parent_labels]
                available = set(G) - set(image.values())
                neighborhoods = [set(G[image[u]]) & available for u in parent_labels]
                _, match, reached, Y = slot_matching(demands, neighborhoods)
                assert len(match) == len(leaves) - 1
                assert {parent_labels[i] for i in reached} == {p}
                assert not Y
                X = {image[p]}
                eta = Fraction(1, 2)
                a = Fraction(2*r - 1, 2)
                incidence = sum(1 for u, v in G.edges() if u in X or v in X)
                internal_core_incidence = sum(1 for u, v in G.subgraph(image.values()).edges()
                                              if u in X or v in X)
                assert incidence == internal_core_incidence == a + eta == r

                # An explicit core change repairs the example; it is NOT T-free.
                image[p], image[q] = image[q], image[p]
                verify_embedding(I, G, image)
                unused = iter(sorted(B - set(image.values())))
                for v in leaves:
                    image[v] = next(unused)
                verify_embedding(T, G, image)
                STATS["bad Hall cores with explicit full-tree repairs"] += 1
        # Independent-set permutations move the singleton Hall parent anywhere in B.
        assert sum(G.degree(v) for v in B) == r*len(B)
        assert r*len(B) > Fraction(2*r - 1, 2)*len(B) + Fraction(1, 2)
        assert all(2*G.degree(v) - G.subgraph(B).degree(v) == 2*r for v in B)
        STATS["nonresistant canonical-Hall unions"] += 1


def root_statistics(W, U, parent):
    """Compute h and M directly from occupied-set polynomials, not from Z(T)."""
    rows = W.polynomial(rooted_shape(U, parent), True)
    scale = W.L**(len(U) - 2)
    h, nonneighbors = [], Fraction(0)
    for v, row in enumerate(rows):
        if not W.deg[v]:
            h.append(Fraction(0))
            continue
        h.append(Fraction(sum(row.values()), scale*W.deg[v]))
        adj = sum(1 << w for w in W.adj[v])
        for mask, coefficient in row.items():
            missing = len(U) - 1 - (mask & adj).bit_count()
            assert missing >= 0
            nonneighbors += Fraction(coefficient*missing, scale*W.deg[v])
    return h, nonneighbors


def covariance_audit():
    negative = 0
    for G0 in nx.graph_atlas_g():
        n = len(G0)
        if n < 3 or any(d == 0 for _, d in G0.degree()):
            continue
        G = nx.convert_node_labels_to_integers(G0)
        m = G.number_of_edges()
        for k in range(2, n):
            eps = 2*m - (k - 1)*n
            if eps not in (1, 2) or not critical(G, k):
                continue
            W = SquareZeroWeight(G)
            for T in nx.nonisomorphic_trees(k + 1):
                zt = W.weight(T)
                seen = set()
                for ell in T:
                    if T.degree(ell) != 1:
                        continue
                    parent = next(iter(T[ell]))
                    U = T.copy()
                    U.remove_node(ell)
                    s = rooted_shape(U, parent)
                    if s in seen:
                        continue
                    seen.add(s)
                    h, M = root_statistics(W, U, parent)
                    zu = W.weight(U)
                    assert zu == sum(d*x for d, x in zip(W.deg, h))
                    assert zt == M + sum((d - k + 1)*x for d, x in zip(W.deg, h))
                    C = n*zu - 2*m*sum(h)
                    pairwise = sum((W.deg[v] - W.deg[w])*(h[v] - h[w])
                                   for v, w in combinations(range(n), 2))
                    assert C == pairwise
                    assert 2*m*zt - eps*zu == 2*m*M + (k - 1)*C
                    negative += C < 0
                    assert 2*m*zt >= eps*zu  # Finite audit only, NOT a proof of CW.
                    STATS["exact critical-host covariance identities"] += 1
    STATS["negative-covariance rooted cases"] = negative

    G = split_host(2)
    T = nx.path_graph(5)
    U = nx.path_graph(4)
    W = SquareZeroWeight(G)
    h, M = root_statistics(W, U, 0)
    assert h[:2] == [Fraction(5, 18)]*2
    assert h[2:] == [Fraction(4, 9)]*5
    assert M == Fraction(20, 9)
    assert W.weight(U) == Fraction(70, 9)
    assert W.weight(T) == Fraction(5, 3)
    assert len(G)*W.weight(U) - 2*G.number_of_edges()*sum(h) == -Fraction(20, 3)

    G = nx.complete_graph(4)
    G.remove_edge(0, 1)
    assert critical(G, 3)
    W = SquareZeroWeight(G)
    U, T = nx.star_graph(2), nx.star_graph(3)
    h, M = root_statistics(W, U, 0)
    variation = sum(abs(h[u] - h[v]) for u, v in G.edges())
    assert M == 0 and variation == Fraction(2, 3)
    assert W.weight(U) == 6 and W.weight(T) == Fraction(4, 3)
    STATS["exact failed scalar shortcuts"] += 2

    # The general star inequality is an algebraic Chebyshev consequence.
    rng = random.Random(548)
    for _ in range(3000):
        n = rng.randrange(2, 40)
        k = rng.randrange(2, 30)
        degrees = [rng.randrange(0, 60) for _ in range(n)]
        two_m = sum(degrees)
        if not two_m:
            continue
        def fall(d, t):
            return math.prod(range(d - t + 1, d + 1)) if d >= t else 0
        h = [Fraction(fall(d, k - 1), d**(k - 1)) if d else Fraction(0) for d in degrees]
        zu = sum(d*x for d, x in zip(degrees, h))
        zt = sum((d - k + 1)*x for d, x in zip(degrees, h))
        C = n*zu - two_m*sum(h)
        assert C >= 0
        assert two_m*zt >= (two_m - (k - 1)*n)*zu
        STATS["exact star-degree Chebyshev audits"] += 1


def matching_roots_nonmatroid_audit():
    G = nx.Graph()
    for block in ([0, 1, 2, 3], [2, 3, 4, 5]):
        G.add_edges_from(combinations(block, 2))
    assert min(dict(G.degree()).values()) == 3
    def feasible(R):
        _, match, _, _ = slot_matching([1]*len(R), [set(G[v]) - set(R) for v in R])
        return len(match) == len(R)
    C1, C2 = {0, 1, 2}, {0, 1, 3}
    assert not feasible(sorted(C1)) and not feasible(sorted(C2))
    for C in (C1, C2):
        for size in range(len(C)):
            assert all(feasible(list(S)) for S in combinations(C, size))
    assert feasible([1, 2, 3])
    # Circuits C1,C2 contain 0, but their union minus 0 is independent.
    STATS["root-selection matroid counterexamples"] += 1


def saturation_arithmetic_audit():
    for k in range(3, 101):
        a = Fraction(k - 1, 2)
        for Delta in range(2, k + 1):
            bound = Fraction(k + 1, 2) - Delta
            for eps in range(1, 2*k + 1):
                eta = Fraction(eps, 2)
                delta_lower = math.ceil(a + eta)
                assert (eta <= bound) == (delta_lower <= k - Delta)
                if eta > bound:
                    assert delta_lower - 1 >= k - Delta
                STATS["saturated surplus/parity identities"] += 1
        r = k // 2
        bound = Fraction(k + 1, 2) - r
        assert bound == (1 if k % 2 else Fraction(1, 2))


def main():
    start = time.time()
    before = lean_hashes()
    assert before["Spec.lean"] == SPEC_SHA
    for name, function in [
        ("independent prescribed roots", independent_root_audit),
        ("different-list star Hall algorithm", star_hall_audit),
        ("canonical one-leaf Hall defects", canonical_hall_audit),
        ("critical cross-core Hall family", hall_core_family_audit),
        ("weighted covariance/nonneighbor decomposition", covariance_audit),
        ("nonmatroid root choices", matching_roots_nonmatroid_audit),
        ("saturated minimal-counterexample arithmetic", saturation_arithmetic_audit),
    ]:
        mark = time.time()
        function()
        print("PASS", name, "seconds", round(time.time() - mark, 3), flush=True)
    assert lean_hashes() == before
    print("\nExact audit totals:")
    for key, value in sorted(STATS.items()):
        print(f"  {value:,} {key}")
    print("  all shared Lean hashes unchanged")
    print("  Spec.lean SHA-256", SPEC_SHA)
    print("elapsed seconds", round(time.time() - start, 3))
    print("STATUS: partial mathematical progress; unrestricted ES and general CW remain unproved.")


if __name__ == "__main__":
    main()
