"""Independent finite consistency checks for Erdos74BufferedColoring.md.

Requires NetworkX.  No SAT/MILP solver and no mathematical assertions are
imported from the preceding amplification check script.
"""
from collections import deque
from itertools import combinations, permutations, product
from math import isqrt
import random
import networkx as nx


def edge(u, v):
    return (min(u, v), max(u, v))


def endpoints(F):
    return {v for e in F for v in e}


def multi_dist(G, roots, cutoff=None):
    ds = dict.fromkeys(roots, 0)
    todo = deque(roots)
    while todo:
        u = todo.popleft()
        if cutoff is not None and ds[u] >= cutoff:
            continue
        for v in G[u]:
            if v not in ds:
                ds[v] = ds[u] + 1
                todo.append(v)
    return ds


def bad(G, p):
    return {edge(u, v) for u, v in G.edges() if p[u] == p[v]}


def layer_pair(d, r):
    if d <= r + 1:
        return (1, 0)
    if d == r + 2:
        return (1, 2)
    if d == r + 3:
        return (0, 2)
    return (0, 1)


def surgery(G, p0, S, r):
    """Return the surgery if the labelled auxiliary graph is balanced.

    Balancedness is tested rather than assumed.  Every claimed conclusion
    is checked on the actual original graph, including graph distances.
    """
    F = bad(G, p0)
    S = {edge(*e) for e in S}
    assert S <= {edge(*e) for e in G.edges()}
    W = endpoints(F | S)
    P = G.copy()
    P.remove_edges_from(F | S)
    assert not bad(P, p0)
    D = 2 * r + 4
    A = {w: [] for w in W}

    def add(u, v, z):
        A[u].append((v, z))
        A[v].append((u, z))

    for u, v in F | S:
        add(u, v, 1 ^ int((u, v) in S))
    for u in sorted(W):
        ds = multi_dist(P, [u], D)
        for v in W:
            if u < v and v in ds:
                add(u, v, ds[v] % 2)
    q = {}
    for root in sorted(W):
        if root in q:
            continue
        q[root] = 0
        todo = [root]
        while todo:
            u = todo.pop()
            for v, z in A[u]:
                val = q[u] ^ z
                if v in q:
                    if q[v] != val:
                        return None
                else:
                    q[v] = val
                    todo.append(v)
    X = {w for w in W if q[w] != p0[w]}
    Y = W - X
    dsX = multi_dist(P, X)
    inf = float('inf')
    assert all(dsX.get(y, inf) > D for y in Y)
    c = {v: layer_pair(dsX.get(v, inf), r)[p0[v]] for v in G}
    assert all(c[w] == q[w] for w in W)
    assert all(c[u] != c[v] for u, v in P.edges())
    Z = {v for v in G if c[v] == 2}
    assert not any(u in Z and v in Z for u, v in G.edges())
    assert not (Z & W)
    dsW = multi_dist(G, W)
    assert all(r + 2 <= dsW[z] <= r + 3 for z in Z)
    G1 = G.copy()
    G1.remove_nodes_from(Z)
    p1 = {v: c[v] for v in G1}
    assert set(p1.values()) <= {0, 1}
    assert bad(G1, p1) == S
    return G1, p1, Z, F


# All locally possible adjacent-layer/bit configurations, for many widths.
layer_cases = 0
for r in range(33):
    for d, e in product(range(2 * r + 9), repeat=2):
        if abs(d - e) <= 1:
            for b in (0, 1):
                assert layer_pair(d, r)[b] != layer_pair(e, r)[1 - b]
                layer_cases += 1
    # The transition's colour-2 layers are separated from X and from Y.
    for dz in (r + 2, r + 3):
        assert dz >= r + 2
        assert (2 * r + 5) - dz >= r + 2
print('buffered adjacent-layer/bit configurations:', layer_cases)


# Enumerate all simple cycles directly, independently of NetworkX cycle bases.
def cycle_masks(G, es, L):
    index = {e: i for i, e in enumerate(es)}
    vs = sorted(G)
    ans = set()
    for length in range(3, min(L, len(vs)) + 1):
        for subset in combinations(vs, length):
            root = min(subset)
            for tail in permutations([v for v in subset if v != root]):
                if tail[0] > tail[-1]:
                    continue
                cyc = (root,) + tail
                ce = [edge(cyc[i], cyc[(i + 1) % length])
                      for i in range(length)]
                if all(e in index for e in ce):
                    mask = sum(1 << index[e] for e in ce)
                    ans.add((mask, length % 2))
    return sorted(ans)


def support_ok(mask, rows):
    return all(((mask & c).bit_count() % 2) == parity
               for c, parity in rows)


# Every minimum short support, every cut, all graphs through four vertices,
# and the 1024 labelled five-vertex graphs for selected deterministic cuts.
# This checks minimality by brute force, not just local pruning.
locality_cases = 0
pruning_cases = 0
for n in range(2, 6):
    universe = list(combinations(range(n), 2))
    for gm in range(1 << len(universe)):
        G = nx.Graph()
        G.add_nodes_from(range(n))
        es = [e for j, e in enumerate(universe) if gm >> j & 1]
        G.add_edges_from(es)
        all_dist = dict(nx.all_pairs_shortest_path_length(G))
        all_cutvals = list(product((0, 1), repeat=n - 1))
        if n == 5:
            all_cutvals = [all_cutvals[j] for j in (0, 3, 5, 10, 15)]
        for L in range(3, n + 1):
            rows = cycle_masks(G, es, L)
            solutions = [x for x in range(1 << len(es)) if support_ok(x, rows)]
            minimum = min(x.bit_count() for x in solutions)
            minima = [x for x in solutions if x.bit_count() == minimum]
            for vals in all_cutvals:
                p = dict(zip(range(n), (0,) + vals))
                F = bad(G, p)
                UF = endpoints(F)
                for sm in minima:
                    S = {e for j, e in enumerate(es) if sm >> j & 1}
                    A = nx.Graph()
                    A.add_nodes_from(F | S)
                    for cm, parity in rows:
                        meet = [e for j, e in enumerate(es)
                                if (cm >> j & 1) and e in F | S]
                        A.add_edges_from(combinations(meet, 2))
                    assert all(set(comp) & F
                               for comp in nx.connected_components(A)
                               if set(comp) & S)
                    US = endpoints(S)
                    for v in US:
                        assert UF
                        d = min(all_dist[v].get(w, float('inf')) for w in UF)
                        assert d <= len(S) * L
                    locality_cases += 1
                # For every support, removing a component with no F preserves
                # all equations. This tests the delicate homogeneous argument.
                if n <= 4:
                    for sm in solutions:
                        S = {e for j, e in enumerate(es) if sm >> j & 1}
                        A = nx.Graph()
                        A.add_nodes_from(F | S)
                        for cm, parity in rows:
                            meet = [e for j, e in enumerate(es)
                                    if (cm >> j & 1) and e in F | S]
                            A.add_edges_from(combinations(meet, 2))
                        for comp in nx.connected_components(A):
                            comp = set(comp)
                            if not (comp & F):
                                T = S - comp
                                tm = sum(1 << j for j, e in enumerate(es) if e in T)
                                assert support_ok(tm, rows)
                                pruning_cases += 1
print('minimum-support/cut/scale locality checks:', locality_cases)
print('homogeneous support-component pruning checks:', pruning_cases)


# Arbitrary small auxiliary instances: test both consistent and inconsistent
# labels; the consistency cases verify every surgery conclusion independently.
rng = random.Random(747474)
balanced = unbalanced = 0
for _ in range(2400):
    n = rng.randrange(3, 13)
    G = nx.gnp_random_graph(n, rng.uniform(.08, .55),
                            seed=rng.randrange(1 << 30))
    p = {v: rng.randrange(2) for v in G}
    S = {edge(u, v) for u, v in G.edges() if rng.random() < .25}
    r = rng.randrange(7)
    out = surgery(G, p, S, r)
    if out is None:
        unbalanced += 1
    else:
        balanced += 1
print('arbitrary-support surgery checks, balanced/unbalanced:', balanced, unbalanced)


# Genuine non-full short supports, with a tunable large buffer.
long_cycles = 0
for r in (0, 1, 2, 7, 31, 128):
    # t=1; choose the odd cycle longer than the entire short-parity scale.
    L = 8 * (r + 2)
    n = 2 * L + 1
    G = nx.cycle_graph(n)
    p = {v: v % 2 for v in G}
    out = surgery(G, p, set(), r)
    assert out is not None
    G1, p1, Z, F = out
    assert len(F) == 1 and Z and nx.is_bipartite(G1)
    long_cycles += 1
print('long-cycle non-full-support buffered surgeries:', long_cycles)


# A multi-theta block: root path length 2, two short odd paths length 99,
# four long even paths length 9000. Its exact cut cost is min(2,5)=2;
# the short-parity minimum at L=8256 is min(2,1)=1.
def theta_block(start, long_length=9000):
    G = nx.Graph()
    u, v = start, start + 1
    nxt = start + 2
    paths = []
    for length in (2, 99, 99) + (long_length,) * 4:
        inner = list(range(nxt, nxt + length - 1))
        nxt += length - 1
        path = [u] + inner + [v]
        G.add_edges_from(zip(path, path[1:]))
        paths.append(path)
    # u=v=0; every even path alternates. Put each odd path's bad edge
    # in its middle, so the new minimum support is far from the old F.
    p = {u: 0, v: 0}
    for path in paths:
        length = len(path) - 1
        for j, w in enumerate(path[1:-1], 1):
            if length % 2 == 0 or j <= length // 2:
                p[w] = j % 2
            else:
                p[w] = (j - 1) % 2
    F = bad(G, p)
    S = {edge(paths[0][0], paths[0][1])}
    assert len(F) == 2
    return G, p, S, nxt


G0, p0, S0, nxt = theta_block(0)
G2, p2, S2, nxt = theta_block(nxt)
G0 = nx.compose(G0, G2)
p0.update(p2)
S0 |= S2
assert len(bad(G0, p0)) == 4 and len(S0) == 2
# All cycles of a theta are unions of two paths. Check the advertised
# short supports against every such pair, using actual path parities.
lengths = (2, 99, 99, 9000, 9000, 9000, 9000)
L0 = 8 * 4 * (2 ** 8 + 2)
assert L0 == 8256
for i, j in combinations(range(7), 2):
    if lengths[i] + lengths[j] <= L0:
        assert ((i == 0) ^ (j == 0)) == ((lengths[i] + lengths[j]) % 2 == 1)
    if lengths[i] + lengths[j] <= 48:
        assert (lengths[i] + lengths[j]) % 2 == 0

out0 = surgery(G0, p0, S0, r=2 ** 8)
assert out0 is not None
G1, p1, Z0, F0 = out0
assert len(F0) == 4 and len(bad(G1, p1)) == 2 and Z0
# The second support is empty: the original graph has odd girth 101,
# and vertex deletion cannot create a shorter odd cycle.
out1 = surgery(G1, p1, set(), r=1)
assert out1 is not None
G2, p2, Z1, F1 = out1
assert len(F1) == 2 and not bad(G2, p2) and Z1
I = Z0 | Z1
assert not (Z0 & Z1)
assert not any(u in I and v in I for u, v in G0.edges())
assert nx.is_bipartite(G0.subgraph(set(G0) - I))
full_colour = {v: (2 if v in I else p2[v]) for v in G0}
assert all(full_colour[u] != full_colour[v] for u, v in G0.edges())
ds_old = multi_dist(G0, Z0)
assert min(ds_old.get(v, float('inf')) for v in Z1) >= 2
for G, F, Z, S, r in ((G0, F0, Z0, S0, 256),
                       (G1, F1, Z1, set(), 1)):
    ds_F = multi_dist(G, endpoints(F))
    radius_bound = len(S) * (8 * len(F) * (r + 2)) + r + 3
    assert max(ds_F[z] for z in Z) <= radius_bound <= len(F) ** 8
print('two successive non-full-support surgeries:')
print('  original vertices/edges:', len(G0), G0.number_of_edges())
print('  defect counts: 4 -> 2 -> 0; buffer sizes:', len(Z0), len(Z1))
print('  combined third-colour class independent; explicit 3-colouring verified')


# A genuinely four-chromatic graph: a K4 plus two long odd cycles,
# connected by bridges. The first surgery lowers t from 4 to 2; the next
# short-parity certificate finds an ACTUAL K4 subgraph with frustration 2.
J = nx.complete_graph(4)
pj = {0: 0, 1: 0, 2: 1, 3: 1}
SJ = bad(J, pj)
assert len(SJ) == 2
for base in (4, 9005):
    vertices = list(range(base, base + 9001))
    J.add_edges_from(zip(vertices, vertices[1:] + vertices[:1]))
    J.add_edge(0, base)
    pj.update({v: 1 ^ ((v - base) % 2) for v in vertices})
assert len(bad(J, pj)) == 4
out = surgery(J, pj, SJ, 256)
assert out is not None
J1, pj1, Zj, Fj = out
assert len(bad(J1, pj1)) == 2 and Zj
assert set(range(4)) <= set(J1)
core_edges = list(combinations(range(4), 2))
rows = cycle_masks(J1.subgraph(range(4)), core_edges, 48)
assert min(x.bit_count() for x in range(64) if support_ok(x, rows)) == 2
selected = set()

def certificate(D, k):
    if D.bit_count() >= k:
        return
    cm, parity = next((cm, parity) for cm, parity in rows
                      if ((D & cm).bit_count() % 2) != parity)
    selected.add(cm)
    for j in range(6):
        if (cm >> j & 1) and not (D >> j & 1):
            certificate(D | (1 << j), k)

certificate(0, 2)
mask = 0
for cm in selected:
    mask |= cm
H = nx.Graph()
H.add_edges_from(e for j, e in enumerate(core_edges) if mask >> j & 1)
assert min(len(bad(H, dict(zip(range(4), (0,) + vals))))
           for vals in product((0, 1), repeat=3)) == 2
assert all(J.has_edge(*e) for e in H.edges())
assert len(H) == 4 <= 3 ** 32
print('four-chromatic fallback: t=4 -> 2, then actual 4-vertex tau=2 certificate')


# Exact integer versions of the estimates used in the induction.
for t in range(2, 100001):
    m = isqrt(t)
    r = m ** 8
    L = 8 * t * (r + 2)
    assert m < t
    assert L <= 24 * t ** 5
    assert m * L + r + 3 <= t ** 8
    q = m + 1
    assert t < q * q
    assert L <= 24 * q ** 10
for q in range(1, 500):
    assert 2 * (24 * q ** 10) ** q <= (q + 1) ** (16 * q)
    assert q * q <= 2 ** (q + 1)
    assert 17 * q * q < 2 ** (q + 6)
    if q >= 16:
        assert 17 * q * q < 2 ** q
assert 16 ** 240 == 2 ** 960
print('integer radius/scale estimates: all 2 <= t <= 100000')
print('witness-size and explicit-profile estimates: all 1 <= q < 500')
print('ALL CHECKS PASSED')
