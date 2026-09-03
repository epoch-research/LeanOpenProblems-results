"""Constructive audit of PeripheralParentClosure.md.

This is NOT a random search for ES counterexamples. It checks the displayed
constructions, rooted-path rotations, exact inequalities, and explicit
critical split families. No general tree-embedding backtracker is used.
The previously audited protected-star and rooted-star-dominance algorithms
are reused only at their proved full edge budgets.
"""
from collections import Counter, deque
from itertools import combinations
import hashlib
from pathlib import Path

import networkx as nx
from WeightedListForestChecks import (
    protected_star_packing, replace_stars, large_list_embedding,
)

STATS = Counter()


def check_copy(T, G, f):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert set(f.values()) <= set(G)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())


def min_degree(G):
    return min(dict(G.degree()).values())


def greedy(T, G, image):
    image = dict(image)
    assert image and nx.is_connected(T.subgraph(image))
    while len(image) < len(T):
        u, v = next((u, v) for u in image for v in T[u] if v not in image)
        free = set(G[image[u]]) - set(image.values())
        assert free
        image[v] = min(free)
    check_copy(T, G, image)
    return image


def branches(T, root):
    R = T.copy()
    R.remove_node(root)
    result = []
    for C in sorted(nx.connected_components(R), key=lambda C: min(C)):
        child, = set(T[root]) & C
        result.append((T.subgraph(C).copy(), child))
    return result


def boundary_list_forest(G, components, A):
    """Nontrivial components; |A|>=m-1, delta>=e, and an A-boundary edge."""
    e = sum(len(T)-1 for T, root in components)
    m = sum(len(T) for T, root in components)
    assert components and all(len(T) >= 2 for T, root in components)
    assert min_degree(G) >= e and len(A) >= m-1
    x, y = next((x, y) for x in sorted(A) for y in sorted(G[x]) if y not in A)
    a = len(components[0][0])-1
    B = {y} | set(sorted(set(G[x])-{y})[:a-1])
    assert len(B) == a
    available = iter(sorted(A - ({x} | B)))
    reservoirs = [{next(available) for _ in T} for T, root in components[1:]]
    stars = protected_star_packing(
        G, [(x, B)], [len(T)-1 for T, root in components[1:]], reservoirs)
    f = replace_stars(G, components, stars)
    assert all(f[root] in A for T, root in components)
    if len(A) == m-1:
        assert set(f.values()) - A
    STATS['boundary-list forest constructions'] += 1
    return f


def nonleaf_root(T, G, root, x):
    """q-edge nonstar, nonleaf root, connected host delta>=q-1, n>=q+1."""
    q = len(T)-1
    assert nx.is_tree(T) and max(dict(T.degree()).values()) < q
    assert T.degree(root) >= 2 and nx.is_connected(G)
    assert len(G) >= q+1 and min_degree(G) >= q-1
    leaf_children = [v for v in T[root] if T.degree(v) == 1]
    if leaf_children:
        ell = min(leaf_children)
        R = T.copy()
        R.remove_node(ell)
        if G.degree(x) >= q:
            f = greedy(R, G, {root: x})
            STATS['nonleaf lemma: leaf-parent, high image'] += 1
        else:
            assert G.degree(x) == q-1
            w = next(v for v in T[root] if T.degree(v) >= 2)
            z = next(v for v in T[w] if v != root)
            A = set(G[x])
            b, c = next((b, c) for b in sorted(A) for c in sorted(G[b])
                        if c not in A | {x})
            f = greedy(R, G, {root: x, w: b, z: c})
            assert not G.has_edge(x, f[z])
            STATS['nonleaf lemma: occupied nonneighbor'] += 1
        f[ell] = min(set(G[x])-set(f.values()))
    else:
        C = branches(T, root)
        assert all(len(U) >= 2 for U, child in C)
        H = G.copy()
        H.remove_node(x)
        A = set(G[x])
        if len(A) >= q:
            f = large_list_embedding(H, C, [A]*len(C))
            STATS['nonleaf lemma: full branch list'] += 1
        else:
            assert len(A) == q-1
            f = boundary_list_forest(H, C, A)
            STATS['nonleaf lemma: boundary branch list'] += 1
        f[root] = x
    check_copy(T, G, f)
    assert f[root] == x
    return f


def incident(G, X):
    return sum(u in X or v in X for u, v in G.edges())


def double_broom(T, G, spine, h):
    """Return a rooted copy, or the proved closed low-incidence set.

    Every candidate path is checked before deduplication by its endpoint.
    In particular a different occupation at an already seen endpoint is not
    silently discarded if it would permit augmentation.
    """
    u, v = spine[0], spine[-1]
    d, s, t = T.degree(u), T.degree(v), len(spine)-1
    k, e = len(T)-1, len(T)-1-d
    assert d >= 2 and s >= 2 and t >= 2
    assert k == d+s+t-2 and e == t+s-2
    assert min_degree(G) >= e and G.degree(h) >= k
    left = sorted(set(T[u])-{spine[1]})
    right = sorted(set(T[v])-{spine[-2]})
    assert all(T.degree(w) == 1 for w in left+right)
    assert set(T) == set(spine) | set(left) | set(right)
    states, queue = {}, deque()
    answer = None

    def offer(P):
        nonlocal answer
        assert len(P) == t+1 and len(set(P)) == t+1 and P[0] == h
        assert all(G.has_edge(a, b) for a, b in zip(P, P[1:]))
        STATS['occupation paths checked'] += 1
        z = P[-1]
        free = sorted(set(G[z])-set(P))
        if len(free) >= s-1:
            f = dict(zip(spine, P))
            f.update(zip(right, free[:s-1]))
            at_h = sorted(set(G[h])-set(f.values()))
            assert len(at_h) >= d-1
            f.update(zip(left, at_h[:d-1]))
            check_copy(T, G, f)
            assert f[u] == h
            answer = f
            return
        assert G.degree(z) == e
        assert all(G.has_edge(z, y) for y in P[:-1])
        if z not in states:
            states[z] = list(P)
            queue.append(z)

    P = [h]
    while len(P) <= t:
        P.append(min(set(G[P[-1]])-set(P)))
    offer(P)
    while queue and answer is None:
        z = queue.popleft()
        P = states[z]
        for i in range(1, t):
            Q = P[:i]+[P[-1]]+list(reversed(P[i:-1]))
            offer(Q)
            STATS['rooted path rotations checked'] += 1
            if answer is not None:
                break
        if answer is not None:
            break
        assert all(G.has_edge(a, b) for a, b in combinations(P, 2))
        for w in sorted(set(G[z])-set(P)):
            middle = [a for a in P[1:-1]][:t-2]
            offer([h]+middle+[z, w])
            STATS['neighbor-closure path switches checked'] += 1
            if answer is not None:
                break
    if answer is not None:
        STATS['double-broom copies constructed'] += 1
        return answer, None
    R = set(states)
    assert R and h not in R
    assert all(G.degree(z) == e and h in G[z] for z in R)
    assert all(set(G[z]) <= R | {h} for z in R)
    assert all(len(set(G[z]) & R) == e-1 for z in R)
    assert 2*incident(G, R) == (e+1)*len(R) <= (k-1)*len(R)
    STATS['closed regular resistance sets constructed'] += 1
    return None, R


def peripheral_copy(T, G, u, h):
    k, r = len(T)-1, (len(T)-1)//2
    e = k-r
    assert k >= 4 and max(dict(T.degree()).values()) <= r
    assert T.degree(u) == r and G.degree(h) >= k and min_degree(G) >= e
    leaves = sorted(w for w in T[u] if T.degree(w) == 1)
    assert len(leaves) == r-1
    stem = [u, next(w for w in T[u] if w not in leaves)]
    while T.degree(stem[-1]) == 2:
        stem.append(next(w for w in T[stem[-1]] if w != stem[-2]))
    if T.degree(stem[-1]) == 1:
        f, R = double_broom(T, G, stem[:-1], h)
        assert R is None
        STATS['peripheral case: path handle'] += 1
        return f
    w = stem[-1]
    R = T.subgraph(set(T)-set(stem[:-1])-set(leaves)).copy()
    if R.degree(w) == len(R)-1:
        f, X = double_broom(T, G, stem, h)
        assert X is None
        STATS['peripheral case: double broom'] += 1
        return f
    L, E = len(stem)-2, len(R)-1
    assert E == e-L and E >= 3 and L <= r-2
    P = [h]
    while len(P) < len(stem):
        P.append(min(set(G[P[-1]])-set(P)))
    S, z = set(P[:-1]), P[-1]
    H = G.subgraph(set(G)-S).copy()
    C = H.subgraph(nx.node_connected_component(H, z)).copy()
    assert min_degree(C) >= E-1
    assert len(C) >= k-2*len(S)+1 >= E+1
    f = dict(zip(stem[:-1], P[:-1]))
    f.update(nonleaf_root(R, C, w, z))
    free = sorted(set(G[h])-set(f.values()))
    assert len(free) >= r-1
    f.update(zip(leaves, free[:r-1]))
    check_copy(T, G, f)
    assert f[u] == h
    STATS['peripheral case: nonstar remainder'] += 1
    return f


def split_critical(k):
    """Explicit nonuniform d-tree family, with a symbolic sparsity certificate."""
    r = k//2
    d = r if k % 2 == 0 else r+1
    n = r*(r+1)+1 if k % 2 == 0 else (r+1)*(r+2)//2+1
    c = d+1
    G = nx.complete_graph(c)
    for v in range(c, n):
        G.add_node(v)
        omit = (v-c) % c
        G.add_edges_from((v, u) for u in range(c) if u != omit)
    assert G.number_of_edges() == d*n-d*(d+1)//2
    assert 2*G.number_of_edges()-(k-1)*n == (1 if k % 2 == 0 else 2)
    assert min_degree(G) == d
    # This actual elimination order proves d-degeneracy. Apply it to every
    # induced subset; the standard extremal bound below therefore certifies
    # ALL proper subsets, rather than checking only a sample of subsets.
    H = G.copy()
    for v in list(range(c, n))+list(range(c)):
        assert H.degree(v) <= d
        H.remove_node(v)
    for size in range(1, n):
        bound = size*(size-1)//2 if size < d else d*size-d*(d+1)//2
        assert 2*bound <= (k-1)*size
    high = [v for v in G if G.degree(v) >= k]
    assert high and all(v < c for v in high)
    assert all(min_degree(G.subgraph(set(G)-{h})) == d-1 for h in high)
    STATS['explicit full-critical host certificates'] += 1
    return G, high


def root_lemma_audit():
    for q in range(3, 8):
        K = nx.disjoint_union(nx.complete_graph(q), nx.complete_graph(q))
        K.add_edge(q-1, q)
        B = nx.complete_bipartite_graph(q-1, q+1)
        for T in nx.nonisomorphic_trees(q+1):
            if max(dict(T.degree()).values()) == q:
                continue
            for root in T:
                if T.degree(root) < 2:
                    continue
                for G in [K, B]:
                    for x in G:
                        check_copy(T, G, nonleaf_root(T, G, root, x))
                        STATS['rooted nonleaf copies audited'] += 1


def peripheral_audit():
    for k in range(4, 12):
        G, high = split_critical(k)
        r = k//2
        for T in nx.nonisomorphic_trees(k+1):
            if max(dict(T.degree()).values()) > r:
                continue
            I = T.subgraph([v for v in T if T.degree(v) >= 2])
            roots = [v for v in I if I.degree(v) == 1 and T.degree(v) == r]
            if not roots:
                continue
            STATS['admissible unlabelled target trees audited'] += 1
            for u in roots:
                for h in high:
                    check_copy(T, G, peripheral_copy(T, G, u, h))
                    STATS['high-parent copies audited'] += 1


def negative_and_arithmetic_audit():
    # Noncritical windmills audit the actual resistance construction.
    for d in range(2, 8):
        for s in range(2, 7):
            for t in range(2, 7):
                k, e = d+s+t-2, s+t-2
                T = nx.path_graph(t+1)
                j = t+1
                for hub, count in [(0, d-1), (t, s-1)]:
                    for _ in range(count):
                        T.add_edge(hub, j)
                        j += 1
                G = nx.Graph()
                G.add_node(0)
                for i in range((k+e-1)//e):
                    A = list(range(1+i*e, 1+(i+1)*e))
                    G.add_edges_from(combinations(A, 2))
                    G.add_edges_from((0, v) for v in A)
                f, R = double_broom(T, G, list(range(t+1)), 0)
                assert f is None and R
    # Complete arithmetic check of the two parity estimates in a finite range;
    # the proof in the report, not these checks, establishes all parameters.
    for k in range(4, 501):
        r, e = k//2, k-k//2
        for L in range(max(0, e-2)):
            E = e-L
            if E >= 3:
                assert L <= r-2 and k-2*L-1 >= E+1
        for deleted in range(k+1):
            for c in range(1, k+2):
                if c*(c-1)+2*deleted*c > (k-1)*c:
                    assert c >= k-2*deleted+1
    STATS['parity/deletion formula parameter values'] = 497


def double_broom_target(d, s, t):
    T = nx.path_graph(t+1)
    j = t+1
    for hub, count in [(0, d-1), (t, s-1)]:
        for _ in range(count):
            T.add_edge(hub, j)
            j += 1
    return T


def positive_switch_audit():
    # Relabel full-critical split hosts so the first greedy path ends at
    # a minimum-degree vertex. A rotation, not the initial path, augments.
    for k in range(6, 12):
        G, high = split_critical(k)
        r, t = k//2, (2 if k % 2 == 0 else 3)
        s = k-r-t+2
        T = double_broom_target(r, s, t)
        c = (r if k % 2 == 0 else r+1)+1
        low = next(v for v in range(c, len(G))
                   if all(G.has_edge(v, x) for x in range(t)))
        ordered = list(range(t))+[low]
        ordered += sorted(set(G)-set(ordered))
        J = nx.relabel_nodes(G, {v: i for i, v in enumerate(ordered)})
        rotations = STATS['rooted path rotations checked']
        f, R = double_broom(T, J, list(range(t+1)), 0)
        assert f is not None and R is None
        assert STATS['rooted path rotations checked'] > rotations
        STATS['critical copies requiring a path rotation'] += 1
    # Explicit noncritical positive examples exercise the neighbor switch:
    # the only extra neighbor is reached outside the original clique-path.
    for e in range(3, 10):
        for t in range(2, e):
            d, s = e, e-t+2
            T = double_broom_target(d, s, t)
            G = nx.Graph()
            for i in range(2):
                A = list(range(1+i*e, 1+(i+1)*e))
                G.add_edges_from(combinations(A, 2))
                G.add_edges_from((0, v) for v in A)
            G.add_edge(e, e+1)
            switches = STATS['neighbor-closure path switches checked']
            f, R = double_broom(T, G, list(range(t+1)), 0)
            assert f is not None and R is None
            assert STATS['neighbor-closure path switches checked'] > switches
            STATS['positive copies requiring an occupation change'] += 1
    # The two-position list discount really fails, although a boundary exists.
    G = nx.disjoint_union(nx.complete_graph(5), nx.complete_graph(5))
    G.add_edge(4, 5)
    A = set(range(4))
    assert min_degree(G) == 4 and nx.is_connected(G)
    assert any(v not in A for u in A for v in G[u])
    for roots in combinations(A, 2):
        Y = set().union(*(set(G[x])-set(roots) for x in roots))
        assert len(Y) == 3 < 4  # Two 2-leaf demands cannot be matched.
    STATS['two-unit list obstruction center pairs checked'] = 6


def main():
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'
    root_lemma_audit()
    peripheral_audit()
    negative_and_arithmetic_audit()
    positive_switch_audit()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == before
    for key, value in sorted(STATS.items()):
        print(f'{key}: {value}')
    print('PASS: constructed maps, path switches, resistance identities, critical certificates')
    print('No general ES proof follows from these finite audits. No Lean files edited.')


if __name__ == '__main__':
    main()
