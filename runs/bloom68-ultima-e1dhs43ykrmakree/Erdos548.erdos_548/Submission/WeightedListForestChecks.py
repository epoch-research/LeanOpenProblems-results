"""Constructive proof audit for WeightedListForestFindings.md.

No embedding backtracker is used by the construction. The only search in it
is bipartite matching, with Hall witnesses and a strictly decreasing root-set
edge potential. Tree replacement recurses on the total number of edges.
Independent backtracking and finite enumerations below audit the construction;
they are not premises of the mathematical theorem.
"""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import hashlib
import random
import time

import networkx as nx

from GlobalESFreshAttemptChecks import (
    slot_matching, weighted_hall, allocate_reservoirs,
    forest_from_components, small_rooted_forests,
    root_embedding, verify_embedding, disjoint_reservoir_choices,
)

STATS = Counter()
SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def protected_star_packing(G, fixed, demands, reservoirs, trace=None):
    """Lemma 1: frozen centers with movable leaves + flexible reservoirs.

    fixed is [(center, leafset), ...], each leafset nonempty. Those initial
    stars are disjoint and avoid every flexible reservoir. Flexible demands
    may be zero. Every current/flexible center needs degree at least E+q,
    where q is the number of zero flexible demands.

    Return [(center, leafset), ...] in frozen-then-flexible order. The frozen
    centers, but NOT their old leaf sets, are preserved.
    """
    f, p = len(fixed), len(demands)
    assert len(reservoirs) == p
    assert all(a >= 0 for a in demands)
    assert all(len(A) == a + 1 for A, a in zip(reservoirs, demands))
    initial_used = set()
    for x, B in fixed:
        assert B and x not in B and not ({x} | B) & initial_used
        assert B <= set(G[x])
        initial_used |= {x} | B
    all_A = set()
    for A in reservoirs:
        assert not A & (all_A | initial_used)
        all_A |= A
    sizes = [len(B) for _, B in fixed] + list(demands)
    E, q = sum(sizes), sum(a == 0 for a in demands)
    assert all(G.degree(x) >= E + q for x in all_A | {x for x, _ in fixed})
    roots = [x for x, _ in fixed] + [min(A) for A in reservoirs]
    potentials = []
    while True:
        R = set(roots)
        assert len(R) == len(roots)
        phi = G.subgraph(R).number_of_edges()
        if potentials:
            assert phi < potentials[-1]
        potentials.append(phi)
        slots, match, Q, Y = slot_matching(sizes, [set(G[x]) - R for x in roots])
        if len(match) == E:
            leaves = [set() for _ in roots]
            for slot, y in match.items():
                leaves[slots[slot][0]].add(y)
            result = list(zip(roots, leaves))
            assert [x for x, _ in result[:f]] == [x for x, _ in fixed]
            assert all(roots[f+i] in A for i, A in enumerate(reservoirs))
            assert all(len(B) == a and B <= set(G[x]) - R
                       for (x, B), a in zip(result, sizes))
            assert sum(map(len, leaves)) == len(set().union(set(), *leaves))
            STATS['protected star packings'] += 1
            STATS['protected root exchanges'] += len(potentials) - 1
            if fixed:
                STATS['packings with frozen centers'] += 1
                STATS['frozen-center root exchanges'] += len(potentials) - 1
                if q:
                    STATS['packings with frozen centers and isolated flexible roots'] += 1
                STATS['frozen leaf sets changed'] += any(B != old[1] for (_, B), old in zip(result, fixed))
            if q:
                STATS['packings with isolated flexible roots'] += 1
            if trace is not None:
                trace.append({'type': 'stars', 'fixed': f, 'flexible': p, 'isolates': q,
                              'demands': sizes, 'potentials': potentials})
            return result

        J = {j for j in Q if j < f}
        K = {j-f for j in Q if j >= f}
        assert K  # The initial frozen stars already match all their own slots.
        frozen_Y = set().union(set(), *(fixed[j][1] for j in J))
        candidate_union = set().union(set(), *(reservoirs[i] for i in K))
        assert frozen_Y <= Y and not frozen_Y & candidate_union
        assert len(Y) <= sum(sizes[j] for j in Q) - 1
        assert len(Y & candidate_union) <= sum(demands[i] for i in K) - 1
        available = candidate_union - R - Y
        assert available
        z = min(available)
        i = next(i for i in K if z in reservoirs[i])
        old = roots[f+i]
        old_inside = len(set(G[old]) & R)
        new_inside = len(set(G[z]) & (R - {old}))
        assert all(not G.has_edge(z, roots[j]) for j in Q)
        assert old_inside >= E + q - sum(sizes[j] for j in Q) + 1
        assert E + q - sum(sizes[j] for j in Q) >= len(roots) - len(Q)
        assert new_inside <= len(roots) - len(Q) < old_inside
        roots[f+i] = z
        STATS['checked Hall-defect exchange inequalities'] += 1
        assert len(potentials) <= len(roots)*(len(roots)-1)//2


def verify_stars(G, components, packing):
    assert len(components) == len(packing)
    used = set()
    for (T, r), (x, B) in zip(components, packing):
        assert nx.is_tree(T) and r in T and len(T) >= 2
        assert len(B) == T.number_of_edges() == len(T)-1
        assert not ({x} | B) & used and x not in B
        assert B <= set(G[x])
        used |= {x} | B


def replace_stars(G, components, packing, trace=None):
    """Theorem 2: rooted-star dominance, preserving all supplied centers."""
    if not components:
        return {}
    e = sum(T.number_of_edges() for T, r in components)
    assert min(dict(G.degree()).values()) >= e
    verify_stars(G, components, packing)
    bad = [i for i, (T, r) in enumerate(components) if T.degree(r) != len(T)-1]
    if not bad:
        image = {}
        for (T, r), (x, B) in zip(components, packing):
            image[r] = x
            image.update(zip(sorted(set(T)-{r}), sorted(B)))
        STATS['star-only recursion bases'] += 1
    else:
        i = bad[0]
        T, r = components[i]
        x, B = packing[i]
        d = T.degree(r)
        remaining_T = T.copy()
        remaining_T.remove_node(r)
        branches = []
        for C in sorted(nx.connected_components(remaining_T), key=lambda C: min(C)):
            child, = set(T[r]) & C
            branches.append((T.subgraph(C).copy(), child))
        q = sum(len(C) == 1 for C, child in branches)
        assert len(branches) == d and d >= q + 1
        assert sum(len(C) for C, _ in branches) == len(B)
        H = G.copy()
        H.remove_node(x)
        fixed = packing[:i] + packing[i+1:]
        other = components[:i] + components[i+1:]
        reservoirs = []
        remaining = iter(sorted(B))
        for C, child in branches:
            reservoirs.append({next(remaining) for _ in C})
        E = sum(U.number_of_edges() for U, _ in other+branches)
        assert E == e-d < e
        assert min(dict(H.degree()).values(), default=e-1) >= e-1 >= E+q
        stars = protected_star_packing(H, fixed,
                    [C.number_of_edges() for C, child in branches], reservoirs, trace)
        new_components = other + branches
        isolated = {root: y for (C, root), (y, L) in zip(new_components, stars) if len(C) == 1}
        assert len(isolated) == q
        H.remove_nodes_from(isolated.values())
        nontrivial = [(C, root) for C, root in new_components if len(C) > 1]
        stars_nontrivial = [P for (C, root), P in zip(new_components, stars) if len(C) > 1]
        assert min(dict(H.degree()).values(), default=E) >= E
        if trace is not None:
            trace.append({'type': 'replacement', 'edges_before': e, 'edges_after': E,
                          'root_degree': d, 'leaf_children': q,
                          'vertices_deleted': 1+q, 'min_degree': min(dict(H.degree()).values(), default=E)})
        image = replace_stars(H, nontrivial, stars_nontrivial, trace)
        image.update(isolated)
        image[r] = x
        assert all(G.has_edge(x, image[child]) for _, child in branches)
        STATS['non-star root replacements'] += 1
        STATS['deleted isolated child branches'] += q
    for (T, r), (x, B) in zip(components, packing):
        assert image[r] == x
        verify_embedding(T, G, {v: image[v] for v in T})
    assert len(set(image.values())) == len(image) == sum(len(T) for T, r in components)
    return image


def reservoir_embedding(G, components, reservoirs, trace=None):
    e = sum(T.number_of_edges() for T, r in components)
    assert all(len(T) >= 2 for T, r in components)
    assert min(dict(G.degree()).values(), default=e) >= e
    packing = protected_star_packing(G, [], [len(T)-1 for T, r in components], reservoirs, trace)
    image = replace_stars(G, components, packing, trace)
    assert all(image[r] in A for (T, r), A in zip(components, reservoirs))
    return image


def weighted_embedding(G, components, lists, trace=None):
    demands = [len(T)-1 for T, r in components]
    assert weighted_hall([a+1 for a in demands], lists)
    reservoirs = allocate_reservoirs(demands, lists)
    return reservoir_embedding(G, components, reservoirs, trace)


def large_list_embedding(G, components, lists, trace=None):
    m = sum(len(T) for T, r in components)
    assert all(len(A) >= m for A in lists)
    keep = [i for i, (T, r) in enumerate(components) if len(T) >= 2]
    image = weighted_embedding(G, [components[i] for i in keep], [lists[i] for i in keep], trace)
    for (T, r), A in zip(components, lists):
        if len(T) == 1:
            image[r] = min(A - set(image.values()))
    assert len(set(image.values())) == m
    return image


def decompose(F, roots):
    return [(F.subgraph(nx.node_connected_component(F, r)).copy(), r) for r in roots]


def atlas_audit():
    for G in nx.graph_atlas_g():
        if len(G) < 4:
            continue
        deg = min(dict(G.degree()).values())
        for F, roots in small_rooted_forests():
            if len(F) > len(G) or F.number_of_edges() > deg:
                continue
            components = decompose(F, roots)
            sizes = [len(C) for C, _ in components]
            for reservoirs in disjoint_reservoir_choices(tuple(G), sizes):
                image = reservoir_embedding(G, components, reservoirs)
                verify_embedding(F, G, image)
                assert all(image[r] in A for r, A in zip(roots, reservoirs))
                STATS['constructive atlas disjoint-reservoir embeddings'] += 1
            for images in permutations(G, len(roots)):
                slots, match, _, _ = slot_matching([s-1 for s in sizes],
                                        [set(G[v])-set(images) for v in images])
                if len(match) != F.number_of_edges():
                    continue
                leaves = [set() for _ in roots]
                for slot, v in match.items():
                    leaves[slots[slot][0]].add(v)
                image = replace_stars(G, components, list(zip(images, leaves)))
                assert all(image[r] == x for r, x in zip(roots, images))
                assert root_embedding(F, roots, G, images) is not None
                STATS['atlas prescribed-center dominance audits'] += 1


def random_audit(trials):
    rng = random.Random(20260918)
    for trial in range(trials):
        p = rng.randrange(2, 7)
        raw = []
        for _ in range(p):
            n = rng.randrange(2, 9)
            T = nx.random_tree(n, seed=rng)
            raw.append((T, rng.randrange(n)))
        F, roots = forest_from_components(raw)
        components = decompose(F, roots)
        e, m = F.number_of_edges(), len(F)
        n = rng.randrange(m, 2*m+5)
        G = nx.empty_graph(n)
        # Clique/independent blowups with random interfaces, then degree repair.
        groups, remaining = [], list(G)
        rng.shuffle(remaining)
        while remaining:
            t = rng.randrange(1, min(len(remaining), e+2)+1)
            groups.append(remaining[:t])
            remaining = remaining[t:]
        for A in groups:
            if rng.randrange(2):
                G.add_edges_from(combinations(A, 2))
        for i, A in enumerate(groups):
            for B in groups[i+1:]:
                if rng.randrange(3) == 0:
                    G.add_edges_from(product(A, B))
        for v in G:
            choices = list(set(G)-set(G[v])-{v})
            rng.shuffle(choices)
            while G.degree(v) < e:
                G.add_edge(v, choices.pop())
        vertices = list(G)
        rng.shuffle(vertices)
        reservoirs, pos = [], 0
        for C, root in components:
            reservoirs.append(set(vertices[pos:pos+len(C)]))
            pos += len(C)
        # Overlapping arbitrary lists guaranteed to satisfy weighted Hall.
        lists = [A | {v for v in G if rng.randrange(5) == 0} for A in reservoirs]
        trace = []
        image = weighted_embedding(G, components, lists, trace)
        verify_embedding(F, G, image)
        assert all(image[r] in A for r, A in zip(roots, lists))
        if trial < 100:
            assert root_embedding(F, roots, G, [image[r] for r in roots]) is not None
        STATS['random arbitrary-list forest embeddings'] += 1
        # Uniform-large-list version, including randomly many isolated components.
        if trial % 4 == 0:
            q = rng.randrange(1, 4)
            G.add_nodes_from(range(n, n+q))
            for v in range(n, n+q):
                G.add_edges_from((v, w) for w in rng.sample(list(range(n)), e))
            extra = []
            for j in range(q):
                C = nx.empty_graph(0)
                C.add_node(m+j)
                extra.append((C, m+j))
            all_components = components + extra
            M = m+q
            lists = [set(rng.sample(list(G), M)) for _ in all_components]
            image = large_list_embedding(G, all_components, lists)
            for (C, root), A in zip(all_components, lists):
                assert image[root] in A
            STATS['uniform-large-list audits including isolates'] += 1


def core_extension(T, C, G, core_image):
    assert set(core_image) == set(C) and nx.is_connected(T.subgraph(C))
    verify_embedding(T.subgraph(C), G, core_image)
    S = set(core_image.values())
    F = T.copy()
    F.remove_nodes_from(C)
    components, lists = [], []
    for U in nx.connected_components(F):
        attachment, = [(u, v) for u in C for v in T[u] if v in U]
        u, r = attachment
        components.append((F.subgraph(U).copy(), r))
        lists.append(set(G[core_image[u]]) - S)
    k, h, b = T.number_of_edges(), len(C), len(components)
    assert F.number_of_edges() == k+1-h-b
    assert len(F) == k+1-h
    assert min(dict(G.degree()).values()) >= k+1-b
    assert all(G.degree(core_image[u]) >= k for u in C if set(T[u])-set(C))
    H = G.copy()
    H.remove_nodes_from(S)
    assert min(dict(H.degree()).values(), default=F.number_of_edges()) >= F.number_of_edges()
    assert all(len(A) >= len(F) for A in lists)
    image = large_list_embedding(H, components, lists)
    image.update(core_image)
    verify_embedding(T, G, image)
    assert all(image[u] == x for u, x in core_image.items())
    return image


def core_audit():
    rng = random.Random(617)
    # A fully critical 11-edge example with genuinely different apex lists.
    G = nx.complete_graph(6)
    G.add_nodes_from(range(6, 22))
    G.add_edges_from(product(range(6), range(6, 22)))
    G.add_edges_from((6+j, 6+(j+1)%16) for j in range(16))
    G.remove_edges_from((0, v) for v in range(6, 14))
    G.remove_edges_from((1, v) for v in range(14, 22))
    assert G.number_of_edges() == 111 == 5*len(G)+1
    assert sorted(dict(G.degree()).values()) == [7]*16+[13]*2+[21]*4
    T = nx.Graph([(0,1),(0,2),(0,3),(0,4),(4,5),(5,6),
                  (1,7),(1,8),(1,9),(9,10),(10,11)])
    assert nx.is_tree(T) and T.number_of_edges() == 11
    assert max(dict(T.degree()).values()) == 4
    L0, L1 = set(G[0])-{0,1}, set(G[1])-{0,1}
    assert len(L0) == len(L1) == 12 and len(L0 & L1) == 4
    core_extension(T, {0,1}, G, {0:0,1:1})
    explicit = {0:0,1:1,2:17,3:18,4:14,5:15,6:16,
                7:9,8:10,9:6,10:7,11:8}
    verify_embedding(T, G, explicit)
    # Exhaustive vertex-subset audit, independently of the analytic proof.
    low_rows = []
    for Y in range(1<<16):
        y = Y.bit_count()
        low_edges = sum(bool(Y & (1<<j)) and bool(Y & (1<<((j+1)%16)))
                        for j in range(16))
        low_rows.append((y,low_edges,(Y & 255).bit_count(),(Y >> 8).bit_count()))
    for C in range(1<<6):
        x = C.bit_count()
        for Y,(y,low_edges,y0,y1) in enumerate(low_rows):
            if C == 63 and Y == 65535:
                continue
            edges = x*(x-1)//2+x*y+low_edges-(y0 if C&1 else 0)-(y1 if C&2 else 0)
            assert edges <= 5*(x+y)
            STATS['critical two-apex proper vertex-set inequalities'] += 1
    # No full-host one-apex certificate at any high vertex for this target.
    for x in range(6):
        assert min(G.degree(v)-G.has_edge(x,v) for v in G if v != x) == 6 < 11-4
    STATS['critical distinct-list two-apex extension examples'] += 1
    # Arbitrary trees and connected cores in hosts with the precise degree budget.
    for _ in range(500):
        k = rng.randrange(3, 20)
        T = nx.random_tree(k+1, seed=rng)
        C = {rng.randrange(k+1)}
        for _ in range(rng.randrange(k)):
            frontier = set().union(*(set(T[u]) for u in C))-C
            if not frontier:
                break
            C.add(rng.choice(sorted(frontier)))
        if len(C) == k+1:
            continue
        b = sum(1 for u in C for v in T[u] if v not in C)
        n = rng.randrange(k+1, 2*k+3)
        G = nx.empty_graph(n)
        for v in G:
            choices = list(set(G)-set(G[v])-{v})
            rng.shuffle(choices)
            while G.degree(v) < k+1-b:
                G.add_edge(v, choices.pop())
        vertices = rng.sample(list(G), len(C))
        image = dict(zip(sorted(C), vertices))
        G.add_edges_from((image[u], image[v]) for u,v in T.subgraph(C).edges())
        for u in C:
            if not set(T[u])-C:
                continue
            v = image[u]
            choices = list(set(G)-set(G[v])-{v})
            rng.shuffle(choices)
            while G.degree(v) < k:
                G.add_edge(v, choices.pop())
        core_extension(T, C, G, image)
        STATS['arbitrary connected-core extensions'] += 1
    # Literal-bound critical K_{r+1,b}: no eligible path-core degree budget.
    for r in range(2, 10):
        b = r*(r+1)+1
        assert (r+1)*b-r*(r+1+b) == 1
        for x in range(r+2):
            for y in range(b+1):
                if (x,y) != (r+1,b):
                    assert x*y <= r*(x+y)
                    STATS['critical bipartite proper-set type inequalities'] += 1
        assert r+1 < 2*r  # No connected-core budget certificate for P_{2r+2}.
        STATS['critical hosts without an eligible path-core budget'] += 1


def explicit_exchange_audit():
    # In the recursive step itself, both frozen centers and isolated child
    # branches are present and the root potential really must decrease.
    G = nx.Graph()
    G.add_edges_from(combinations([0,1,3,4,5],2))
    G.add_edges_from(combinations([2,6,7,8,9],2))
    G.add_edges_from((10,v) for v in range(10))
    T = nx.Graph([(0,1),(1,2),(0,3),(0,4)])
    U = nx.Graph([(5,6)])
    components = [(T,0),(U,5)]
    packing = [(10,{1,2,3,4}),(0,{5})]
    trace = []
    image = replace_stars(G, components, packing, trace)
    assert image[0] == 10 and image[5] == 0
    assert any(t['type'] == 'stars' and t['fixed'] == 1 and t['isolates'] == 2
               and t['potentials'] == [6,3] for t in trace)
    assert any(t['type'] == 'replacement' and t['edges_before'] == 5
               and t['edges_after'] == 2 and t['vertices_deleted'] == 3 for t in trace)
    STATS['explicit frozen-center, isolated-branch exchange examples'] += 1


def boundary_audit():
    # Zero-demand components require the separate extra-degree/list-room rule.
    for q in range(1, 8):
        G = nx.complete_graph(q+2)
        G.remove_edge(0,1)
        F = nx.Graph([(0,1)])
        F.add_nodes_from(range(2,q+2))
        lists = [{0,1}]+[{v} for v in range(2,q+2)]
        assert weighted_hall([2]+[1]*q, lists)
        assert min(dict(G.degree()).values()) == q
        assert all(root_embedding(F, [0]+list(range(2,q+2)), G,
                    [x]+list(range(2,q+2))) is None for x in (0,1))
        STATS['sharp isolated-component counterexamples'] += 1
    # Only candidate degrees are insufficient for arbitrary rooted trees.
    G = nx.disjoint_union_all([nx.path_graph(3)]*3)
    roots = [1,4,7]
    assert all(G.degree(v) == 2 for v in roots)
    assert all(root_embedding(nx.path_graph(3), [0], G, [v]) is None for v in roots)
    STATS['root-candidate-only degree counterexamples'] += 1
    # Star feasibility is sufficient but not necessary for a specific shape.
    G = nx.disjoint_union(nx.complete_graph(5), nx.complete_graph(5))
    G.add_edge(4,5)
    F, rr = forest_from_components([(nx.path_graph(3),0)]*2)
    _, match, _, _ = slot_matching([2,2], [set(G[x])-{0,1} for x in [0,1]])
    assert len(match) == 3
    image = root_embedding(F, rr, G, [0,1])
    assert image is not None
    verify_embedding(F, G, image)
    STATS['star-feasibility nonnecessity examples'] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--random', type=int, default=3000)
    parser.add_argument('--skip-atlas', action='store_true')
    args = parser.parse_args()
    start = time.time()
    before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in Path(__file__).parent.glob('*.lean')}
    assert before['Spec.lean'] == SPEC_SHA
    jobs = [('boundary qualifications', boundary_audit),
            ('explicit protected-center recursive exchange', explicit_exchange_audit)]
    if not args.skip_atlas:
        jobs.append(('exhaustive atlas construction', atlas_audit))
    jobs += [('random deeper rooted forests', lambda: random_audit(args.random)),
             ('connected-core and critical-host corollaries', core_audit)]
    for name, job in jobs:
        mark = time.time()
        job()
        print('PASS', name, 'seconds', round(time.time()-mark,3), flush=True)
    after = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in Path(__file__).parent.glob('*.lean')}
    assert before == after
    for key, value in sorted(STATS.items()):
        print(f'{value:,} {key}', flush=True)
    print('Shared Lean files unchanged; Spec SHA-256', SPEC_SHA)
    print('Elapsed seconds', round(time.time()-start,3))
    print('The general theorems are proved in WeightedListForestFindings.md, not by these finite audits.')
    print('Unrestricted Erdos--Sos and automatic adaptive-core selection are NOT claimed.')


if __name__ == '__main__':
    main()
