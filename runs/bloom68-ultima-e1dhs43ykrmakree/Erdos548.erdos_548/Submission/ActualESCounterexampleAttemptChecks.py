#!/usr/bin/env python3
"""Exact, construction-led checks for ActualESCounterexampleAttempt.md.

No candidate-graph search and no timeout-based noncontainment conclusions.
The one negative embedding computation is a complete capacitated quotient DP
for the explicitly proved bridge trap. All positive copies are checked
edge-by-edge. No Lean source or other report is modified.

Run: python3 Submission/ActualESCounterexampleAttemptChecks.py
Optional independent all-subsets audit (integer min cuts): add --mincut.
"""
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations, product
import argparse
import hashlib
from pathlib import Path
import time
import networkx as nx


COUNTS = {}


def count(key, amount=1):
    COUNTS[key] = COUNTS.get(key, 0) + amount


def target(p, q=None, arity=2):
    """Adjacent hubs, p and q supports, arity leaves per support."""
    if q is None:
        q = p
    T = nx.Graph()
    T.add_edge(('h', 0), ('h', 1))
    for side, branches in enumerate((p, q)):
        for j in range(branches):
            s = ('s', side, j)
            T.add_edge(('h', side), s)
            for t in range(arity):
                T.add_edge(s, ('l', side, j, t))
    assert nx.is_tree(T)
    assert T.number_of_edges() == (arity + 1) * (p + q) + 1
    return T


def verify_copy(T, G, phi):
    assert set(phi) == set(T)
    assert len(set(phi.values())) == len(T)
    assert set(phi.values()) <= set(G)
    assert all(G.has_edge(phi[u], phi[v]) for u, v in T.edges())
    count('verified full non-induced tree copies')


@dataclass
class Chamber:
    A: list
    B: list


def chamber_graph(p, q, arity=2, number=3, internal_cliques=False):
    assert (arity - 1) * q <= p <= arity * q
    assert number >= 1
    G = nx.Graph()
    chambers = []
    for i in range(number):
        A = [('A', i, j) for j in range(arity * q)]
        B = [('B', i, j) for j in range(arity * p + 1)]
        chambers.append(Chamber(A, B))
        G.add_nodes_from(A + B)
        G.add_edges_from(product(A, B))
        if internal_cliques:
            G.add_edges_from(combinations(A, 2))
            G.add_edges_from(combinations(B, 2))
    return G, chambers


def put_branch(phi, side, supports, leaves, arity):
    assert len(leaves) == arity * len(supports)
    for j, s in enumerate(supports):
        phi[('s', side, j)] = s
        for t in range(arity):
            phi[('l', side, j, t)] = leaves[arity * j + t]


def bb_copy(p, q, arity, chambers, i, b0, j, b1):
    assert i != j
    phi = {('h', 0): b0, ('h', 1): b1}
    put_branch(phi, 0, chambers[i].A[:p],
               [v for v in chambers[i].B if v != b0][:arity * p], arity)
    put_branch(phi, 1, chambers[j].A[:q],
               [v for v in chambers[j].B if v != b1][:arity * q], arity)
    return phi


def two_arc_copy(p, q, arity, chambers, i, b0, j, a1, b1, ell, a2):
    """Use B_i--A_j as the hub edge, B_j--A_ell as one leaf edge."""
    assert i != j and ell != j
    phi = {('h', 0): b0, ('h', 1): a1}
    first_supports = [v for v in chambers[i].A if v != a2][:p]
    assert len(first_supports) == p  # Also checks the return-walk spare slot.
    put_branch(phi, 0, first_supports,
               [v for v in chambers[i].B if v != b0][:arity * p], arity)
    second_supports = [b1] + [v for v in chambers[j].B if v != b1][:q - 1]
    second_leaves = [a2] + [v for v in chambers[j].A if v != a1]
    put_branch(phi, 1, second_supports, second_leaves, arity)
    return phi


def internal_b_edge_copy(p, q, arity, chambers, i, b0, j, a1, u, v):
    """One incoming interface and one internal B_j edge free the missing leaf."""
    assert i != j and u != v
    phi = {('h', 0): b0, ('h', 1): a1}
    put_branch(phi, 0, chambers[i].A[:p],
               [z for z in chambers[i].B if z != b0][:arity * p], arity)
    supports = [u] + [z for z in chambers[j].B if z not in (u, v)][:q - 1]
    put_branch(phi, 1, supports, [v] + [z for z in chambers[j].A if z != a1], arity)
    return phi


def incidence(G, X):
    X = set(X)
    return sum(u in X or v in X for u, v in G.edges())


def chamber_certificate(G, p, q, arity, chambers):
    """Return a full copy OR an exact low-incidence set, not a T-free verdict."""
    assert arity >= 2 and q >= 1
    assert (arity - 1) * q <= p <= arity * q
    assert chambers
    loc = {}
    for i, C in enumerate(chambers):
        assert len(C.A) == arity * q and len(C.B) == arity * p + 1
        assert all(G.has_edge(a, b) for a in C.A for b in C.B)
        for typ, vs in (('A', C.A), ('B', C.B)):
            for v in vs:
                assert v not in loc
                loc[v] = (typ, i)
    assert set(loc) == set(G)
    outgoing = [[] for _ in chambers]
    for u, v in G.edges():
        tu, i = loc[u]
        tv, j = loc[v]
        if i == j:
            continue
        if tu == tv == 'B':
            return 'copy-BB', bb_copy(p, q, arity, chambers, i, u, j, v)
        if tu == 'B' and tv == 'A':
            outgoing[i].append((u, j, v))
        elif tv == 'B' and tu == 'A':
            outgoing[j].append((v, i, u))
    for i, arcs in enumerate(outgoing):
        for b0, j, a1 in arcs:
            internal = next(iter(G.subgraph(chambers[j].B).edges()), None)
            if internal is not None:
                u, v = internal
                return 'copy-internal-B-edge', internal_b_edge_copy(
                    p, q, arity, chambers, i, b0, j, a1, u, v)
            for b1, ell, a2 in outgoing[j]:
                if ell != i or p < arity * q:
                    return 'copy-two-arcs', two_arc_copy(
                        p, q, arity, chambers, i, b0, j, a1, b1, ell, a2)
    sink = next((i for i, arcs in enumerate(outgoing) if not arcs), None)
    if sink is None:
        assert p == arity * q
        # Every directed component is a closed 2-cycle. Both B sets are
        # independent: otherwise the preceding internal-edge repair applies.
        i = 0
        partner = outgoing[i][0][1]
        assert all(j == partner for _, j, _ in outgoing[i])
        assert all(j == i for _, j, _ in outgoing[partner])
        assert G.subgraph(chambers[i].B).number_of_edges() == 0
        B = set(chambers[i].B)
        assert incidence(G, B) <= 2 * arity * q * len(B)
        kind = 'low-incidence-two-cycle'
    else:
        B = set(chambers[sink].B)
        kind = 'low-incidence'
    a = Fraction((arity + 1) * (p + q), 2)
    assert incidence(G, B) <= a * len(B)
    return kind, B


def audit_chambers():
    for arity in range(2, 5):
        for q in range(1, 6):
            for p in range((arity - 1) * q, arity * q + 1):
                T = target(p, q, arity)
                base, C = chamber_graph(p, q, arity)
                for x, y in product((0, -1), repeat=2):
                    b0, b1 = C[0].B[x], C[1].B[y]
                    G = base.copy()
                    G.add_edge(b0, b1)
                    verify_copy(T, G, bb_copy(p, q, arity, C, 0, b0, 1, b1))
                for ell in (0, 2):
                    if ell == 0 and p == arity * q:
                        continue  # Exactly the collision handled by the 2-cycle charge.
                    for u, v, w, z in product((0, -1), repeat=4):
                        b0, a1 = C[0].B[u], C[1].A[v]
                        b1, a2 = C[1].B[w], C[ell].A[z]
                        G = base.copy()
                        G.add_edges_from(((b0, a1), (b1, a2)))
                        verify_copy(T, G, two_arc_copy(
                            p, q, arity, C, 0, b0, 1, a1, b1, ell, a2))
                        count('return-walk repairs' if ell == 0 else 'three-chamber repairs')
                G = base.copy()
                b0, a1 = C[0].B[0], C[1].A[0]
                u, v = C[1].B[0], C[1].B[-1]
                G.add_edges_from(((b0, a1), (u, v)))
                verify_copy(T, G, internal_b_edge_copy(p, q, arity, C, 0, b0, 1, a1, u, v))
                if p == arity * q:
                    G2, C2 = chamber_graph(p, q, arity, number=2)
                    G2.add_edges_from(product(C2[0].B, C2[1].A))
                    G2.add_edges_from(product(C2[1].B, C2[0].A))
                    kind, cert = chamber_certificate(G2, p, q, arity, C2)
                    assert kind == 'low-incidence-two-cycle'
                    count('capacity-tight two-cycle incidence certificates')
                count('analytic chamber parameter triples')
    # Exhaust only the six abstract interface arcs on three fixed chambers.
    # A low-incidence output does NOT claim the graph is T-free.
    p = q = arity = 2
    T = target(p, q, arity)
    base, C = chamber_graph(p, q, arity, internal_cliques=True)
    possible = [(i, j) for i in range(3) for j in range(3) if i != j]
    for mask in range(1 << len(possible)):
        for add_bb in (False, True):
            G = base.copy()
            for bit, (i, j) in enumerate(possible):
                if mask >> bit & 1:
                    G.add_edge(C[i].B[0], C[j].A[-1])
            if add_bb:
                G.add_edge(C[0].B[-1], C[1].B[-1])
            kind, cert = chamber_certificate(G, p, q, arity, C)
            if kind.startswith('copy'):
                verify_copy(T, G, cert)
            else:
                assert incidence(G, cert) <= 6 * len(cert)
                count('explicit low-incidence outputs')
            count('complete three-module interface patterns')


def critical_family(d, number=7):
    """Quota-oriented chambers; every A has one missing antipodal partner."""
    assert d >= 2 and number >= 5
    G = nx.Graph()
    D = nx.DiGraph()
    C = []
    for i in range(number):
        A = [('A', i, j) for j in range(2 * d)]
        B = [('B', i, j) for j in range(2 * d + 1)]
        C.append(Chamber(A, B))
        G.add_nodes_from(A + B)
        D.add_nodes_from(A + B)

    def arc(u, v):
        assert u != v and not G.has_edge(u, v)
        G.add_edge(u, v)
        D.add_edge(u, v)

    for i, Q in enumerate(C):
        for j in range(2 * d):
            for h in range(1, d):
                arc(Q.A[j], Q.A[(j + h) % (2 * d)])
        for j in range(2 * d + 1):
            for h in range(1, d + 1):
                arc(Q.B[j], Q.B[(j + h) % (2 * d + 1)])
        for a, b in product(Q.A, Q.B):
            arc(a, b)
        for b in Q.B:
            for step in (1, 2):
                for a in C[(i + step) % number].A[:d]:
                    arc(b, a)
    assert nx.is_strongly_connected(D)
    assert set(dict(D.out_degree()).values()) == {3 * d}
    root = C[0].B[0]
    exceptional_low = C[3].A[d]
    arc(root, exceptional_low)
    return G, D, C, root, exceptional_low


def audit_critical_family():
    rows = []
    for d, m in ((2, 5), (3, 5), (5, 6), (7, 7), (11, 7)):
        G, D, C, root, exceptional_low = critical_family(d, m)
        T = target(d)
        k, r, n = 6 * d + 1, 3 * d, m * (4 * d + 1)
        assert len(G) == n >= k + 1
        assert G.number_of_edges() == r * n + 1
        assert all(D.out_degree(v) == r + (v == root) for v in G)
        assert len(nx.descendants(D, root)) + 1 == n
        high_A = {v for Q in C for v in Q.A[:d]}
        low_A = {v for Q in C for v in Q.A[d:]}
        Bs = {v for Q in C for v in Q.B}
        assert all(G.degree(v) == 8 * d + 1 for v in high_A)
        assert all(G.degree(v) == 4 * d - 1 + (v == exceptional_low) for v in low_A)
        assert all(G.degree(v) == 6 * d + (v == root) for v in Bs)
        assert not nx.is_bipartite(G)
        # Independently check the complete neighborhood identities used in
        # the global (arbitrary bipartition) colored-core exclusion proof.
        for i, Q in enumerate(C):
            for j, v in enumerate(Q.A):
                expected = set(Q.A) - {v, Q.A[(j + d) % (2 * d)]}
                expected |= set(Q.B)
                if j < d:
                    expected |= set(C[(i - 1) % m].B + C[(i - 2) % m].B)
                if v == exceptional_low:
                    expected.add(root)
                assert set(G[v]) == expected
            for v in Q.B:
                expected = (set(Q.B) - {v}) | set(Q.A)
                expected |= set(C[(i + 1) % m].A[:d] + C[(i + 2) % m].A[:d])
                if v == root:
                    expected.add(exceptional_low)
                assert set(G[v]) == expected
        core_numbers = nx.core_number(G)
        assert max(core_numbers.values()) == 5 * d <= k - 2
        assert len(nx.k_core(G, k=k - 1)) == 0
        H = G.subgraph(set(G) - low_A)
        assert all(H.degree(v) == 5 * d for v in Bs)
        assert min(dict(H.degree()).values()) == 5 * d
        high = {v for v in G if G.degree(v) >= k}
        assert high == high_A | {root}
        high_graph = G.subgraph(high)
        assert {v for v in high if high_graph.degree(v) >= d + 1} == {root}
        # Exact local inequalities used to exclude EVERY balanced colored core.
        assert 6 * d + 1 > 4 * d + 1
        assert 2 * d + 2 < 3 * d + 1
        assert 5 * d + 1 < 2 * (3 * d + 1)
        assert 5 * d < k - 2 and 4 * d < k - 2
        kind, phi = chamber_certificate(G, d, d, 2, C)
        assert kind.startswith('copy')
        verify_copy(T, G, phi)
        # An explicitly specified copy uses NO added surplus edge.
        explicit = two_arc_copy(d, d, 2, C, 0, C[0].B[0], 1, C[1].A[0],
                                C[1].B[0], 2, C[2].A[0])
        G0 = G.copy()
        G0.remove_edge(root, exceptional_low)
        verify_copy(T, G0, explicit)
        rows.append((d, k, n, G.number_of_edges(), 5 * d))
        count('full critical orientation and terminal-exclusion audits')
    print('CRITICAL FAMILY (d,k,n,e,degeneracy):', rows, flush=True)


def closure_surplus(G, r, omitted=None):
    """Exact integer max closure: max_S(e(S)-r|S|), optionally S omits a vertex."""
    F = nx.DiGraph()
    source, sink = ('source',), ('sink',)
    M = G.number_of_edges() + r * len(G) + 2
    for j, (u, v) in enumerate(G.edges()):
        e = ('edge', j)
        F.add_edge(source, e, capacity=1)
        F.add_edge(e, ('vertex', u), capacity=M)
        F.add_edge(e, ('vertex', v), capacity=M)
    for v in G:
        F.add_edge(('vertex', v), sink, capacity=M if v == omitted else r)
    cut, _ = nx.minimum_cut(F, source, sink,
                            flow_func=nx.algorithms.flow.preflow_push)
    assert isinstance(cut, int)
    return G.number_of_edges() - cut


def audit_mincuts():
    for d, m in ((2, 5), (7, 7)):
        G, _, C, _, _ = critical_family(d, m)
        assert closure_surplus(G, 3 * d) == 1
        count('integer max-closure certificates')
        # All omissions for both graphs: this independently covers ALL proper S.
        for v in G:
            assert closure_surplus(G, 3 * d, v) == 0
            count('integer max-closure certificates')
        print('ALL PROPER SUBSETS VIA INTEGER MIN CUT:', d, len(G), flush=True)


def bridge_trap(d, b=None):
    assert d >= 2
    if b is None:
        b = 4 * d + 3
    C = [('C', j) for j in range(6 * d - 2)]
    A = [('A', j) for j in range(2 * d)]
    B = [('B', j) for j in range(b)]
    G = nx.Graph()
    G.add_nodes_from(C + A + B)
    G.add_edges_from(combinations(C, 2))
    G.add_edges_from(combinations(A[1:], 2))
    G.add_edges_from(product(A, B))
    G.add_edge(C[0], A[0])
    return G, C, A, B


def trap_bb_copy(d, A, B, x, y):
    phi = {('h', 0): x, ('h', 1): y}
    leaves = [v for v in B if v not in (x, y)][:4 * d]
    put_branch(phi, 0, A[:d], leaves[:2 * d], 2)
    put_branch(phi, 1, A[d:], leaves[2 * d:], 2)
    return phi


def trap_bc_copy(d, C, A, B, x, y):
    phi = {('h', 0): x, ('h', 1): y}
    put_branch(phi, 0, A[:d], [v for v in B if v != x][:2 * d], 2)
    rest = [v for v in C if v != y]
    put_branch(phi, 1, rest[:d], rest[d:3 * d], 2)
    return phi


def four_leaf_copy(T, C, matching):
    assert len(matching) == 4
    assert len({u for u, _ in matching}) == len({v for _, v in matching}) == 4
    parents = [v for v in T if v[0] == 's'][:4]
    leaves = [('l', p[1], p[2], 0) for p in parents]
    phi = {}
    for p, l, (c, a) in zip(parents, leaves, matching):
        phi[p], phi[l] = c, a
    spare = iter(v for v in C if v not in phi.values())
    for v in T:
        if v not in phi:
            phi[v] = next(spare)
    return phi


def quotient_dp(T, capacities, adjacency):
    """Complete occupancy DP; clique types have loops, independent types do not.

    Uniform complete interfaces make a capacity-respecting homomorphism exactly
    equivalent to an injective non-induced embedding into this mixed blow-up.
    Every state is retained; no numerical pruning or timeout is used.
    """
    root = next(iter(T))
    parent = {root: None}
    order = [root]
    for u in order:
        for v in T[u]:
            if v != parent[u]:
                parent[v] = u
                order.append(v)
    q = len(capacities)
    dp, shape_cache, shapes = {}, {}, {}
    states = products = 0
    for u in reversed(order):
        children = [v for v in T[u] if parent.get(v) == u]
        shape = tuple(sorted((shapes[v] for v in children), key=repr))
        shapes[u] = shape
        if shape in shape_cache:
            dp[u] = shape_cache[shape]
            continue
        result = []
        for i in range(q):
            initial = tuple(int(t == i) for t in range(q))
            current = {initial} if capacities[i] else set()
            for v in children:
                options = set().union(*(dp[v][j] for j in adjacency[i]))
                new = set()
                for x in current:
                    for y in options:
                        products += 1
                        z = tuple(x[t] + y[t] for t in range(q))
                        if all(z[t] <= capacities[t] for t in range(q)):
                            new.add(z)
                current = new
                if not current:
                    break
            result.append(current)
            states += len(current)
        dp[u] = result
        shape_cache[shape] = result
    return sum(map(len, dp[root])), states, products


def audit_quotient_dp():
    # Independent complete enumeration of color assignments, solely to audit
    # the capacity DP on small fixed mixed-blow-up models.
    models = [((2, 3, 2), ({1}, {0, 1, 2}, {1})),
              ((2, 2, 2), ({1, 2}, {0, 2}, {0, 1})),
              ((1, 3, 2), ({0, 1}, {0, 2}, {1, 2}))]
    for n in range(2, 8):
        for T0 in nx.nonisomorphic_trees(n):
            T = nx.convert_node_labels_to_integers(T0)
            for caps, adj in models:
                root = next(iter(T))
                exact = set()
                for colors in product(range(3), repeat=n):
                    occupancy = tuple(colors.count(i) for i in range(3))
                    if any(occupancy[i] > caps[i] for i in range(3)):
                        continue
                    if all(colors[v] in adj[colors[u]] for u, v in T.edges()):
                        exact.add((colors[root], occupancy))
                feasible, _, _ = quotient_dp(T, caps, adj)
                assert feasible == len(exact)
                count('DP versus complete color-assignment audits')
    # A deliberate positive control for the 44-vertex target: completing B
    # to a clique must destroy the negative verdict for the bridge template.
    positive_adj = ({1, 2}, {0, 1}, {0, 4}, {3, 4}, {2, 3, 4})
    feasible, _, _ = quotient_dp(target(7), (1, 39, 1, 13, 31), positive_adj)
    assert feasible > 0
    count('positive 44-vertex capacity DP controls')


def audit_bridge_traps():
    rows = []
    for d in range(2, 13):
        T = target(d)
        G, C, A, B = bridge_trap(d)
        b, k, r = len(B), 6 * d + 1, 3 * d
        assert len(G) == 12 * d + 1 >= k + 1
        assert G.number_of_edges() == 28 * d * d - 12 * d + 5
        deficit = r * len(G) - G.number_of_edges()
        assert deficit == 8 * d * d + 15 * d - 5 > 0
        assert max(dict(G.degree()).values()) == k
        assert not nx.is_bipartite(G)
        assert max(nx.core_number(G).values()) == k - 4
        assert incidence(G, B) == 2 * d * b < r * b
        # All target edges fall into the three cases of the bridge proof.
        sizes = set()
        for u, v in T.edges():
            Q = T.copy()
            Q.remove_edge(u, v)
            sizes.add(tuple(sorted(map(len, nx.connected_components(Q)))))
        assert sizes == {(1, 6 * d + 1), (3, 6 * d - 1), (3 * d + 1, 3 * d + 1)}
        assert len(C) < 6 * d - 1
        assert 3 * d - 1 > len(A) and 2 * d + 1 > len(A)
        assert len(nx.max_weight_matching(T, maxcardinality=True)) == 2 * d + 1
        for leaf in [v for v in T if T.degree(v) == 1]:
            Q = T.copy()
            Q.remove_node(leaf)
            assert len(nx.max_weight_matching(Q, maxcardinality=True)) == 2 * d + 1
            count('leaf-deleted matching witnesses')
        # Every missing edge incident with B is an immediate unrooted repair.
        pairs_bb = list(combinations(B, 2)) if d <= 4 else [(B[0], B[-1])]
        pairs_bc = list(product(B, C)) if d <= 4 else [(B[0], C[0]), (B[-1], C[-1])]
        for x, y in pairs_bb:
            J = G.copy()
            J.add_edge(x, y)
            verify_copy(T, J, trap_bb_copy(d, A, B, x, y))
            count('individual forbidden B--B completion edges')
        for x, y in pairs_bc:
            J = G.copy()
            J.add_edge(x, y)
            verify_copy(T, J, trap_bc_copy(d, C, A, B, x, y))
            count('individual forbidden B--C completion edges')
        for shift in range(min(6, len(C))):
            for perm in permutations(range(4)):
                M = [(C[(shift + j) % len(C)], A[perm[j]]) for j in range(4)]
                J = G.copy()
                J.add_edges_from(M)
                verify_copy(T, J, four_leaf_copy(T, C, M))
                count('four-leaf matching completion repairs')
        # The all-supergraphs upper bound, not an ES assumption.
        bound = len(C) * (len(C) - 1) // 2 + len(A) * (len(A) - 1) // 2
        bound += 3 * len(C) + 2 * d * b
        assert bound == 20 * d * d + 2 * d - 3 + 2 * d * b
        assert r * len(G) - bound == 4 * d * d - 8 * d + 3 + d * b > 0
        for x in range(4):
            for y in range(4 - x):
                assert x * len(A) + y * len(C) - x * y <= 3 * len(C)
        if d in (2, 3, 7):
            rows.append((d, k, len(G), G.number_of_edges(), deficit, bound))
        count('proved all-role bridge-trap parameter audits')
    print('T-FREE TRAPS (d,k,n,e,deficit,all-completion upper bound):', rows, flush=True)
    # Five exact quotient types: C-bridge vertex, other C, port, other A, B.
    adj = ({1, 2}, {0, 1}, {0, 4}, {3, 4}, {2, 3})
    for d in (2, 3, 4, 7):
        caps = (1, 6 * d - 3, 1, 2 * d - 1, 4 * d + 3)
        feasible, states, products = quotient_dp(target(d), caps, adj)
        assert feasible == 0
        count('exhausted negative capacity DPs')
        count('exact quotient DP retained states', states)
        count('exact quotient DP transitions', products)
        print('EXACT ALL-ROLE TRAP DP:', d, 'feasible', feasible,
              'states', states, 'transitions', products, flush=True)


def parity_core(T, M, c, chosen_root=None):
    used = set()
    blocks = []
    for u, v in M:
        assert u not in used and v not in used and T.has_edge(u, v)
        blocks.append({u, v})
        used.update((u, v))
    unmatched = set(T) - used
    assert len(unmatched) <= 1
    if unmatched:
        blocks.append(unmatched)
        start = len(blocks) - 1
        howmany = len(M) - c + 1
    else:
        start = next(i for i, B in enumerate(blocks) if chosen_root in B)
        howmany = len(M) - c
        assert howmany >= 1
    loc = {v: i for i, B in enumerate(blocks) for v in B}
    Q = nx.Graph()
    Q.add_nodes_from(range(len(blocks)))
    Q.add_edges_from((loc[u], loc[v]) for u, v in T.edges() if loc[u] != loc[v])
    assert nx.is_tree(Q)
    order = list(nx.bfs_tree(Q, start))
    R = set().union(*(blocks[i] for i in order[:howmany]))
    assert nx.is_connected(T.subgraph(R))
    dist = nx.multi_source_dijkstra_path_length(T, R, weight=None)
    U = {v for v in T if dist[v] % 2}
    W = set(T) - R - U
    assert len(U) == len(W) == c
    assert all(set(T[w]) <= U for w in W)
    assert not any(u in U and v in U for u, v in T.edges())
    if not unmatched:
        assert chosen_root in R
    count('exact matching-block parity kernels')


def audit_parity_and_matching():
    T = target(7)
    assert len(T) == 44 and T.number_of_edges() == 43
    assert max(dict(T.degree()).values()) == 8
    assert len(nx.max_weight_matching(T, maxcardinality=True)) == 15
    independent = {v for v in T if v[0] == 'l'} | {('h', 0)}
    assert len(independent) == 29
    assert not any(u in independent and v in independent for u, v in T.edges())
    spectrum = {20, 21, 22}
    min19 = 100
    for hubs, maxa, offset in ((1, 7, 22), (2, 14, 14)):
        for a in range(maxa + 1):
            for b in range(2 * a + 1):
                size, odd = hubs + a + b, offset + a - b
                if size <= 6:
                    spectrum.add(odd)
                if odd == 19:
                    min19 = min(min19, size)
    assert spectrum == set(range(13, 19)) | set(range(20, 28))
    assert min19 == 7
    count('exact 44-vertex parity-spectrum audits')
    for m in range(2, 18):
        for base in (nx.path_graph(m), nx.star_graph(m - 1), nx.balanced_tree(2, 2)):
            R = nx.convert_node_labels_to_integers(base)
            h = len(R)
            S = R.copy()
            M = [(v, h + v) for v in range(h)]
            S.add_edges_from(M)
            for root in (0, h - 1, h):
                for c in range(1, h):
                    parity_core(S, M, c, root)
            S.add_edge(0, 2 * h)  # The existing M is now near-perfect.
            for c in range(1, h + 1):
                parity_core(S, M, c)
    print('PARITY GAP: odd spectrum at core budget 6 =', sorted(spectrum),
          '; minimum core for odd count 19 =', min19, flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mincut', action='store_true')
    args = parser.parse_args()
    start = time.time()
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    audit_chambers()
    audit_critical_family()
    audit_bridge_traps()
    audit_quotient_dp()
    audit_parity_and_matching()
    if args.mincut:
        audit_mincuts()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == before
    print('COUNTS:')
    for key, value in sorted(COUNTS.items()):
        print(' ', key + ':', value)
    print('Spec.lean SHA256:', before)
    print('PASS; seconds:', round(time.time() - start, 3))
    print('STATUS: no ES counterexample and no unrestricted ES proof.')


if __name__ == '__main__':
    main()
