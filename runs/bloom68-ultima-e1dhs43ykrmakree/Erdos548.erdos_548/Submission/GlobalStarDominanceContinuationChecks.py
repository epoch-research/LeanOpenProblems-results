"""Small constructive audits for GlobalStarDominanceContinuation.md.

No graph-atlas search, parameter sweep, or ES embedding oracle is used.
The universal assertions are proved in the report.  This only checks the
budget arithmetic and the displayed constructions, including repeated chambers.
"""
from itertools import product
import networkx as nx

from WeightedListForestChecks import (
    protected_star_packing, replace_stars, verify_stars, verify_embedding,
)


def discounted_embedding(G, components, packing, selected):
    selected = set(selected)
    verify_stars(G, components, packing)
    e = sum(T.number_of_edges() for T, _ in components)
    g = 0
    branches, reservoirs = [], []
    restored = {}
    for i in sorted(selected):
        T, r = components[i]
        x, B = packing[i]
        q_i = sum(T.degree(v) == 1 for v in T[r])
        h_i = T.degree(r) - q_i
        assert h_i >= 1
        g += h_i - 1
        restored[r] = x
        R = T.copy()
        R.remove_node(r)
        leaves = iter(sorted(B))
        for C in sorted(nx.connected_components(R), key=min):
            child, = set(T[r]) & C
            U = T.subgraph(C).copy()
            branches.append((U, child))
            reservoirs.append({next(leaves) for _ in C})
    assert min(dict(G.degree()).values()) >= e - g
    frozen = [i for i in range(len(components)) if i not in selected]
    new_components = [components[i] for i in frozen] + branches
    H = G.copy()
    H.remove_nodes_from(restored.values())
    E = sum(T.number_of_edges() for T, _ in new_components)
    q = sum(len(T) == 1 for T, _ in branches)
    assert E == e - sum(components[i][0].degree(components[i][1]) for i in selected)
    assert e - g - len(selected) == E + q
    assert min(dict(H.degree()).values()) >= E + q
    stars = protected_star_packing(
        H, [packing[i] for i in frozen],
        [T.number_of_edges() for T, _ in branches], reservoirs,
    )
    isolated = {r: x for (T, r), (x, _) in zip(new_components, stars) if len(T) == 1}
    H.remove_nodes_from(isolated.values())
    assert min(dict(H.degree()).values()) >= E
    nontrivial = [(T, r) for T, r in new_components if len(T) > 1]
    certificates = [P for (T, _), P in zip(new_components, stars) if len(T) > 1]
    f = replace_stars(H, nontrivial, certificates)
    f.update(isolated)
    f.update(restored)
    assert len(set(f.values())) == sum(len(T) for T, _ in components)
    for (T, r), (x, _) in zip(components, packing):
        verify_embedding(T, G, {v: f[v] for v in T})
        assert f[r] == x
    return e, g, len(selected), q, E


def subdivided_star(d, offset):
    T = nx.Graph()
    for j in range(d):
        T.add_edges_from([(offset, offset + 2*j + 1),
                          (offset + 2*j + 1, offset + 2*j + 2)])
    return T, offset


def audit_discount():
    components = [subdivided_star(2, 0), subdivided_star(2, 10)]
    G = nx.complete_bipartite_graph(6, 8)
    packing = [(0, set(range(6, 10))), (1, set(range(10, 14)))]
    assert discounted_embedding(G, components, packing, [0, 1]) == (8, 2, 2, 0, 4)
    bad = nx.complete_bipartite_graph(5, 8)
    verify_stars(bad, components, [(0, set(range(5, 9))), (1, set(range(9, 13)))])
    assert sum(1 + (len(T)-1)//2 for T, _ in components) == 6 > 5
    mixed = nx.Graph([(0, 1), (1, 2), (0, 3), (3, 4), (0, 5)])
    path = nx.Graph([(10, 11), (11, 12)])
    G = nx.complete_bipartite_graph(6, 7)
    assert discounted_embedding(
        G, [(mixed, 0), (path, 10)],
        [(0, set(range(6, 11))), (1, {11, 12})], [0],
    ) == (7, 1, 1, 1, 4)
    print('Discount: two constructive examples, including a frozen component and an isolated branch; sharpness K_{5,8}.')


def audit_punctured_stars():
    r, k = 2, 5
    G = nx.complete_bipartite_graph(3, 7)
    T = nx.path_graph(6)
    assert G.number_of_edges() == r*len(G) + 1 == 21
    for x, y in product(range(4), range(8)):
        if (x, y) != (3, 7):
            assert x*y <= r*(x+y)
    for s in range(3):
        for u in T:
            assert k - T.degree(u) > r  # all prescribed centers are in the large part
        P = [s] + [v for v in range(3) if v != s]
        f = {2*i: P[i] for i in range(3)}
        f.update({2*i+1: 3+i for i in range(3)})
        verify_embedding(T, G, f)
    print('Punctured-star obstruction: K_{3,7}, all 18 (high vertex, hole) choices; 31 proper subset types; full path copies verified.')


def chambers(c, number):
    G = nx.Graph()
    A = [{(i, 'A', j) for j in range(c)} for i in range(number)]
    B = [{(i, 'B', j) for j in range(c+1)} for i in range(number)]
    for i in range(number):
        G.add_nodes_from(A[i] | B[i])
        G.add_edges_from(product(A[i], B[i]))
    return G, A, B


def split_halves(T, x, y):
    R = T.copy()
    R.remove_edge(x, y)
    return [T.subgraph(nx.node_connected_component(R, r)).copy() for r in (x, y)]


def place_half(T, root, same_palette, opposite_palette, fixed, avoid=()):
    distance = nx.single_source_shortest_path_length(T, root)
    same = {v for v, d in distance.items() if d % 2 == 0}
    opposite = set(T) - same
    f = dict(fixed)
    for labels, palette in [(same, same_palette), (opposite, opposite_palette)]:
        for v in sorted(labels - set(f)):
            available = set(palette) - set(f.values()) - set(avoid)
            assert available
            f[v] = min(available)
    return f


def check_join(T, G, f, g):
    assert not set(f) & set(g)
    image = f | g
    verify_embedding(T, G, image)


def arm_tree(d):
    T = nx.Graph([(0, 1)])
    v = 2
    for root in (0, 1):
        for _ in range(d):
            T.add_edges_from([(root, v), (v, v+1), (v+1, v+2)])
            v += 3
    return T


def deep_exception():
    T = nx.Graph([(0, 10)])
    for o in (0, 10):
        T.add_edges_from([(o, o+1), (o+1, o+2), (o+2, o+3)] +
                         [(o+3, o+j) for j in (4, 5, 6)])
    return T


def audit_chamber_certificates():
    T = arm_tree(2)
    U, V = split_halves(T, 0, 1)
    G, A, B = chambers(4, 2)
    G.add_edge((0, 'B', 0), (1, 'A', 0))
    check_join(T, G,
        place_half(U, 0, B[0], A[0], {0: (0, 'B', 0)}),
        place_half(V, 1, A[1], B[1], {1: (1, 'A', 0)}))

    T = deep_exception()
    U, V = split_halves(T, 0, 10)
    for mode in ('BB', 'internal', 'return'):
        G, A, B = chambers(4, 2)
        donor = {0: (0, 'B', 0)}
        if mode == 'BB':
            G.add_edge((0, 'B', 0), (1, 'B', 0))
            f = place_half(U, 0, B[0], A[0], donor)
            g = place_half(V, 10, B[1], A[1], {10: (1, 'B', 0)})
        else:
            G.add_edge((0, 'B', 0), (1, 'A', 0))
            leaf_image = (1, 'B', 1) if mode == 'internal' else (0, 'A', 0)
            G.add_edge((1, 'B', 0), leaf_image)
            f = place_half(U, 0, B[0], A[0], donor, avoid={leaf_image})
            g = place_half(V, 10, A[1], B[1],
                           {10: (1, 'A', 0), 13: (1, 'B', 0), 14: leaf_image})
        check_join(T, G, f, g)

    T = nx.path_graph(10)
    U, V = split_halves(T, 4, 5)
    G, A, B = chambers(2, 3)
    G.add_edges_from([((0, 'B', 0), (1, 'A', 0)), ((1, 'B', 0), (2, 'A', 0))])
    check_join(T, G,
        place_half(U, 4, B[0], A[0], {4: (0, 'B', 0)}),
        place_half(V, 5, A[1], B[1], {5: (1, 'A', 0), 8: (1, 'B', 0), 9: (2, 'A', 0)}))
    G, A, B = chambers(2, 2)
    G.add_edges_from(product(B[0], A[1]))
    G.add_edges_from(product(B[1], A[0]))
    for part in B:
        incidence = sum(u in part or v in part for u, v in G.edges())
        assert incidence == 4*len(part) == 12
        assert all(2*G.degree(v) - len(set(G[v]) & part) == 8 for v in part)
    G, A, B = chambers(4, 2)
    for part in B:
        G.add_edges_from((x, y) for x in part for y in part if x < y)
    assert all(2*G.degree(v) - len(set(G[v]) & B[0]) == 12 for v in B[0])
    print('Chambers: five full-copy certificates, including a depth-four repair leaf and a two-chamber return; tight sink and two-cycle W-resistance checked.')


def audit_critical_application():
    d, m = 2, 5
    G, A, B = chambers(2*d, m)
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for i in range(m):
        for j in range(2*d):
            for offset in range(1, d):
                D.add_edge((i, 'A', j), (i, 'A', (j+offset) % (2*d)))
        for j in range(2*d+1):
            for offset in range(1, d+1):
                D.add_edge((i, 'B', j), (i, 'B', (j+offset) % (2*d+1)))
        D.add_edges_from(product(A[i], B[i]))
        for offset in (1, 2):
            D.add_edges_from(product(B[i], {((i+offset) % m, 'A', j) for j in range(d)}))
    s = (0, 'B', 0)
    D.add_edge(s, (3, 'A', d))
    G = D.to_undirected()
    assert all(D.out_degree(v) == 3*d + (v == s) for v in G)
    assert len(nx.descendants(D, s)) == len(G)-1
    assert D.number_of_edges() == G.number_of_edges()  # no opposite orientations
    T = arm_tree(d)
    k = T.number_of_edges()
    leaves = sum(T.degree(v) == 1 for v in T)
    assert (len(G), G.number_of_edges(), min(dict(G.degree()).values())) == (45, 271, 7)
    assert G.number_of_edges() == (k-1)*len(G)//2 + 1
    assert min(dict(G.degree()).values()) + leaves == 11 < k+1 == 14
    U, V = split_halves(T, 0, 1)
    high = {v for v in G if G.degree(v) >= k}
    for z in high:
        if z == s:
            i, j, x, y = 0, 1, s, (1, 'A', 0)
        else:
            j = z[0]
            i = (j-1) % m
            x, y = (i, 'B', 0), z
        f = place_half(U, 0, B[i], A[i], {0: x})
        g = place_half(V, 1, A[j], B[j], {1: y})
        check_join(T, G, f, g)
        assert z in set(f.values()) | set(g.values())
    print('Critical application: n=45, e=271=6n+1, delta=7; root-reachable quota certificate; all 11 high vertices covered; every coarse core budget fails.')


if __name__ == '__main__':
    audit_discount()
    audit_punctured_stars()
    audit_chamber_certificates()
    audit_critical_application()
    print('All targeted audits passed. No exhaustive tree/host search was run.')
