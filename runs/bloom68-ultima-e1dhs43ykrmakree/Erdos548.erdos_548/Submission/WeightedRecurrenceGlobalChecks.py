"""Exact, targeted audits for WeightedRecurrenceGlobalFindings.md.

This does NOT prove or disprove the proposed critical-host recurrence (CW).
It checks a structural obstruction to bounded-block weighted transport, and
an exact construction of additional critical hosts.  The large examples are
certified by integer inequalities and the proved formulas, not enumeration.
No Lean file is imported or modified.

Run: python3 Submission/WeightedRecurrenceGlobalChecks.py
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import hashlib
import heapq
import math
import time

import networkx as nx

SPEC_SHA = '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'


def falling(n, j):
    return math.prod(range(n-j+1, n+1)) if 0 <= j <= n else 0


def split_host(r, deficit=None):
    # deficit=None is critical; deficit=0 or 1 is the padding core.
    b = r*r+1 if deficit is None else r*r-deficit
    G = nx.empty_graph(r+b)
    G.add_edges_from((i, j) for i in range(r) for j in range(i+1, r+b))
    return G


def rooted_parents(R, root):
    order, parent = [root], {root: None}
    for u in order:
        for v in R[u]:
            if v not in parent:
                parent[v] = u
                order.append(v)
    assert len(order) == len(R)
    return order, parent


def target_from_rooted_tree(R, root=0):
    """H=R+ell, T=subdivision(H), U=T-ell; m_v is v's matching partner."""
    assert set(R) == set(range(len(R))) and nx.is_tree(R)
    r = len(R)
    _, parent = rooted_parents(R, root)
    ell = r
    mate = {v: r+1+v for v in R}
    T = nx.empty_graph(2*r+1)
    for v in R:
        T.add_edge(v, mate[v])
        T.add_edge(ell if parent[v] is None else parent[v], mate[v])
    U = T.copy()
    U.remove_node(ell)
    return T, U, ell, mate[root], mate


def binary_original_tree(h):
    R = nx.balanced_tree(2, h)
    H = R.copy()
    H.add_edge(0, len(R))
    return H


def delete_leaf_and_root(H, ell):
    assert H.degree(ell) == 1
    root = next(iter(H[ell]))
    R = H.copy()
    R.remove_node(ell)
    labels = {v: i for i, v in enumerate(R)}
    return nx.relabel_nodes(R, labels), labels[root]


def ancestor_closed_masks(R, root):
    _, parent = rooted_parents(R, root)

    def rec(v):
        masks = [1 << v]
        for w in R[v]:
            if parent.get(w) == v:
                child = rec(w)
                masks = [x | y for x in masks for y in child]
        return [0] + masks

    return rec(root)


def boundary(R, mask):
    return sum(bool(mask & (1 << u)) != bool(mask & (1 << v))
               for u, v in R.edges())


def rooted_partition(R, root, q):
    _, parent = rooted_parents(R, root)

    def rec(v):
        return math.prod(q + rec(w) for w in R[v] if parent.get(w) == v)

    return rec(root)


def base_mass(r):
    b, D = r*r+1, r*(r+1)
    return Fraction(math.factorial(r)*falling(b, r), D**(r-1)*r**(r-1))


def pattern_predictions(R, root=0):
    r = len(R)
    q = Fraction(1, r+1)
    A = base_mass(r)
    alpha = Fraction(r*r-r+1, r*(r+1))
    C = rooted_partition(R, root, q)
    return A*(1+C), A*alpha


def independent_set_weight(Q, r):
    """General tree independent-set DP, separate from the matching patterns.

    Records (size(I), sum_{v in I}(deg_Q(v)-1)), then sums the exact
    injections into the split host. It also applies directly to the full T.
    """
    root = next(iter(Q))

    def add(a, b):
        c = Counter(a)
        c.update(b)
        return c

    def mul(a, b):
        c = Counter()
        for (i, j), x in a.items():
            for (s, t), y in b.items():
                c[i+s, j+t] += x*y
        return c

    def rec(v, parent):
        yes = Counter({(1, Q.degree(v)-1): 1})
        no = Counter({(0, 0): 1})
        for w in Q[v]:
            if w != parent:
                cy, cn = rec(w, v)
                yes = mul(yes, cn)
                no = mul(no, add(cy, cn))
        return yes, no

    yes, no = rec(root, None)
    n, b, D = len(Q), r*r+1, r*(r+1)
    result = Fraction(0)
    for (i, j), c in add(yes, no).items():
        count = c*falling(b, i)*falling(r, n-i)
        if count:
            result += Fraction(count, r**j * D**(n-2-j))
    return result


def direct_weight_and_escape(Q, G, marked=None):
    """Independent injective backtracking, using integer-scaled weights."""
    deg = dict(G.degree())
    L = math.lcm(*deg.values())
    scale = {v: L//deg[v] for v in G}
    root = max(Q, key=Q.degree) if marked is None else marked
    order, parent = rooted_parents(Q, root)
    image, occupied = {}, set()
    total, escape = 0, 0

    def rec(i, weight):
        nonlocal total, escape
        if i == len(order):
            total += weight
            if marked is not None:
                v = image[marked]
                fresh = sum(w not in occupied for w in G[v])
                escape += weight*fresh*scale[v]
            return
        u = order[i]
        candidates = G if parent[u] is None else G[image[parent[u]]]
        for v in candidates:
            if v not in occupied and deg[v] >= Q.degree(u):
                image[u] = v
                occupied.add(v)
                rec(i+1, weight*scale[v]**(Q.degree(u)-1))
                occupied.remove(v)
                del image[u]

    rec(0, 1)
    return (Fraction(total, L**(len(Q)-2)),
            Fraction(escape, L**(len(Q)-1)))


def audit_patterns_and_weights():
    cases = [(nx.star_graph(r-1), 0) for r in range(2, 9)]
    cases += [(nx.balanced_tree(2, h), 0) for h in range(4)]
    for h in (2, 3):
        H = binary_original_tree(h)
        ell = next(v for v in H if H.degree(v) == 1)
        cases.append(delete_leaf_and_root(H, ell))
    patterns = dp_checks = 0
    for R, root in cases:
        r = len(R)
        T, U, ell, p, mate = target_from_rooted_tree(R, root)
        q, b, D = Fraction(1, r+1), r*r+1, r*(r+1)
        A = base_mass(r)
        masks = ancestor_closed_masks(R, root)
        allowed = set(masks)
        # Every possible one-endpoint-per-matching-edge pattern is checked.
        for W in range(1 << r):
            C = {v for v in R if W & (1 << v)}
            C |= {mate[v] for v in R if not W & (1 << v)}
            I = set(U)-C
            feasible = all(not (u in I and v in I) for u, v in U.edges())
            assert feasible == (W in allowed)
            if not feasible:
                continue
            j = boundary(R, W)
            c_exp = sum(U.degree(v)-1 for v in C)
            i_exp = sum(U.degree(v)-1 for v in I)
            actual = Fraction(math.factorial(r)*falling(b, r),
                              D**c_exp * r**i_exp)
            assert actual == A*q**j
            assert (p in C) == (W == 0)
            # All A vertices are occupied; when p is in A exactly b-r
            # neighbors are fresh, and when p is in B none are fresh.
            factor = Fraction(b-r, D) if p in C else Fraction(0)
            assert factor == (Fraction(r*r-r+1, D) if W == 0 else 0)
            patterns += 1
        total_by_patterns = A*sum(q**boundary(R, W) for W in masks)
        ZU, ZT = pattern_predictions(R, root)
        assert total_by_patterns == ZU
        assert independent_set_weight(U, r) == ZU
        assert independent_set_weight(T, r) == ZT
        assert 2*split_host(r).number_of_edges()*ZT >= ZU
        dp_checks += 2
    # A direct, non-pattern embedding enumeration on three small instances.
    direct_cases = [(nx.star_graph(1), 0), (nx.star_graph(2), 0),
                    (nx.path_graph(3), 0)]
    for R, root in direct_cases:
        T, U, ell, p, mate = target_from_rooted_tree(R, root)
        G = split_host(len(R))
        ZU, ZT = pattern_predictions(R, root)
        gotU, escape = direct_weight_and_escape(U, G, marked=p)
        gotT, _ = direct_weight_and_escape(T, G)
        assert gotU == ZU and gotT == ZT and escape == ZT
    print('Matching-pattern/weight/escape audits:', patterns)
    print('Independent-set DP comparisons:', dp_checks)
    print('Independent direct weighted embedding and leaf-identity cases:',
          len(direct_cases))


def mask_neighbors(mask, n, allowed, block=1):
    for j in range(1, block+1):
        for vertices in combinations(range(n), j):
            other = mask
            for v in vertices:
                other ^= 1 << v
            if other in allowed:
                yield other


def minimax_boundary(R, root=0):
    allowed = set(ancestor_closed_masks(R, root))
    full = (1 << len(R))-1
    dist = {full: 0}
    queue = [(0, full)]
    while queue:
        level, W = heapq.heappop(queue)
        if dist[W] != level:
            continue
        if W == 0:
            return level
        for X in mask_neighbors(W, len(R), allowed):
            candidate = max(level, boundary(R, X))
            if candidate < dist.get(X, len(R)+1):
                dist[X] = candidate
                heapq.heappush(queue, (candidate, X))
    raise AssertionError('Full-to-empty pattern path should exist')


def audit_transport_barriers():
    for h in range(4):
        R = nx.balanced_tree(2, h)
        got = minimax_boundary(R)
        expected = 0 if h == 0 else h+1
        assert got == expected
        print('Binary height', h, 'vertices', len(R),
              'exact nonmonotone minimax boundary', got)

    all_leaf_audits = 0
    for h in (2, 3):
        H = binary_original_tree(h)
        got_barriers = Counter()
        for ell in H:
            if H.degree(ell) != 1:
                continue
            R, root = delete_leaf_and_root(H, ell)
            assert max(dict(R.degree()).values()) <= 3
            got = minimax_boundary(R, root)
            assert got >= h
            got_barriers[got] += 1
            all_leaf_audits += 1
        print('All-leaf binary height', h, 'barrier distribution:',
              sorted(got_barriers.items()))
    print('Independent all-leaf minimax audits:', all_leaf_audits)

    R = nx.balanced_tree(2, 3)
    r, q = len(R), Fraction(1, len(R)+1)
    all_masks = set(ancestor_closed_masks(R, 0))
    for block in (1, 2):
        # One change in W corresponds to two changed images in Emb(U,G).
        t = 4-2*(block-1)
        low = {W for W in all_masks if boundary(R, W) < t}
        reachable, queue = {0}, deque([0])
        while queue:
            W = queue.popleft()
            for X in mask_neighbors(W, r, low, block):
                if X not in reachable:
                    reachable.add(X)
                    queue.append(X)
        assert (1 << r)-1 not in reachable
        high_mass_over_A = sum(q**boundary(R, W) for W in all_masks
                               if boundary(R, W) >= t)
        assert high_mass_over_A <= Fraction(2, math.factorial(t))
        print('Binary height 3, image block', 2*block, 'cut threshold', t,
              'cut mass/A =', high_mass_over_A)

    # Small explicit obstruction: not a counterexample to CW.
    r = 5
    q = Fraction(1, r+1)
    twice_m = r*(2*r*r+r+1)
    congestion = q**(-(r-1))
    alpha = Fraction(r*r-r+1, r*(r+1))
    cw_margin = twice_m*alpha/(1+(1+q)**(r-1))
    assert congestion == 1296 and twice_m == 280
    assert congestion > twice_m and cw_margin > 1
    print('Star-derived r=5: two-image transport congestion >=', congestion,
          '> 2m =', twice_m, '; actual CW margin =', cw_margin)

    # No giant graph/tree is built here. This is an exact integer audit of
    # the parameter instance in the proved infinite subcubic family.
    h = 24
    r = 2**(h+1)-1
    t = h+1  # sharp for two-image updates, i.e. one W-vertex at a time
    twice_m = r*(2*r*r+r+1)
    congestion = math.factorial(t)//2
    assert congestion > twice_m
    print('Subcubic height 24: r =', r, 'k =', 2*r,
          'n =', r*r+r+1)
    print('  congestion >= 25!/2 =', congestion,
          '> 2m =', twice_m,
          '; certified ratio =', Fraction(congestion, twice_m))
    all_leaf_congestion = math.factorial(h)//2
    assert all_leaf_congestion > twice_m
    print('  EVERY leaf: congestion >= 24!/2 =', all_leaf_congestion,
          '> 2m; certified ratio =', Fraction(all_leaf_congestion, twice_m))


def induced_edges_by_mask(G):
    assert set(G) == set(range(len(G)))
    rows = [sum(1 << w for w in G[v]) for v in G]
    edges = [0]*(1 << len(G))
    for mask in range(1, len(edges)):
        bit = mask & -mask
        v, rest = bit.bit_length()-1, mask-bit
        edges[mask] = edges[rest] + (rows[v] & rest).bit_count()
    return edges


def audit_critical(G, k):
    eps = 2*G.number_of_edges()-(k-1)*len(G)
    assert eps in (1, 2)
    e = induced_edges_by_mask(G)
    assert all(2*e[S] <= (k-1)*S.bit_count()
               for S in range((1 << len(G))-1))
    return eps


def prism_plus_diagonal(length):
    assert length >= 3
    G = nx.empty_graph(2*length)
    for i in range(length):
        G.add_edge(i, (i+1) % length)
        G.add_edge(length+i, length+(i+1) % length)
        G.add_edge(i, length+i)
    G.add_edge(0, length+1)
    return G


def padding_host(r, h, F):
    epsF = 2*F.number_of_edges()-(2*(r-h)-1)*len(F)
    assert 1 <= h < r and epsF in (1, 2)
    gamma = epsF-1
    core = split_host(r, deficit=gamma)
    offset = len(core)
    G = core.copy()
    G.add_nodes_from(offset+v for v in F)
    G.add_edges_from((offset+u, offset+v) for u, v in F.edges())
    G.add_edges_from((i, offset+v) for i in range(h) for v in F)
    return G, gamma


def audit_critical_families():
    split_types = 0
    for r in range(1, 9):
        b, n = r*r+1, r*r+r+1
        assert r*(2*r*r+r+1) == (2*r-1)*n+1
        for x in range(r+1):
            for y in range(b+1):
                if x+y < n:
                    assert x*(x-2*r)+(2*x-2*r+1)*y <= 0
                    split_types += 1

    F1 = nx.complete_graph(5)
    F1.remove_edges_from([(0, 1), (2, 3)])
    F2 = prism_plus_diagonal(3)
    cases = [(2, 1, nx.path_graph(3)), (3, 1, F1),
             (3, 1, F2), (4, 2, F2)]
    padding_types = 0
    for r, h, F in cases:
        epsF = audit_critical(F, 2*(r-h))
        G, gamma = padding_host(r, h, F)
        b = r*r-gamma
        assert gamma == epsF-1
        assert 2*G.number_of_edges() == (2*r-1)*len(G)+1
        fe = induced_edges_by_mask(F)
        for xh in range(h+1):
            for xc in range(r-h+1):
                x = xh+xc
                for y in range(b+1):
                    for S, edge_count in enumerate(fe):
                        z = S.bit_count()
                        size = x+y+z
                        surplus = (x*(x-1)+2*x*y+2*edge_count+2*xh*z
                                   -(2*r-1)*size)
                        if size < len(G):
                            assert surplus <= 0
                        else:
                            assert surplus == 1
                        padding_types += 1
        if len(G) <= 9:
            assert audit_critical(G, 2*r) == 1
        print('Padding audit: k =', 2*r, 'n =', len(G), 'epsilon_F =', epsF,
              'outer epsilon = 1, degrees =', sorted(Counter(dict(G.degree()).values()).items()))
    # Arbitrary-length prism construction is proved in the note. A few
    # small independent direct induced-set audits check its implementation.
    for length in (3, 4, 5):
        assert audit_critical(prism_plus_diagonal(length), 4) == 2
    print('Critical split proper-subset types:', split_types)
    print('Critical padding subset types:', padding_types)


def audit_scalar_identities():
    G = split_host(2)
    k, eta = 4, Fraction(1, 2)
    a = Fraction(k-1, 2)
    potentials = [list(map(Fraction, row)) for row in
                  [[0]*len(G), [1]*len(G), list(range(len(G))),
                   [0, 1, 0, 2, 0, 3, 1], [2, 0, 5, 1, 2, 0, 4]]]
    for x in potentials:
        lo = sum(min(x[u], x[v]) for u, v in G.edges())
        hi = sum(max(x[u], x[v]) for u, v in G.edges())
        assert lo <= a*sum(x)+eta*min(x)
        assert hi >= a*sum(x)+eta*max(x)
    # Free-attachment aggregate, not a prescribed-parent recurrence.
    U = nx.path_graph(4)
    ZU = independent_set_weight(U, 2)
    total = Fraction(0)
    for p in U:
        Q = U.copy()
        Q.add_edge(p, 4)
        total += independent_set_weight(Q, 2)
    assert total >= ZU/(len(G)-1)
    print('Exact scalar-potential audits:', len(potentials),
          '; free-attachment aggregate audit: passed')


def main():
    started = time.time()
    spec = Path(__file__).with_name('Spec.lean')
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA
    audit_critical_families()
    audit_patterns_and_weights()
    audit_transport_barriers()
    audit_scalar_identities()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA
    print('Spec.lean unchanged:', SPEC_SHA)
    print('All targeted exact checks passed in %.2f seconds.' % (time.time()-started))
    print('CW and unrestricted Erdős–Sós remain unproved and unrefuted here.')


if __name__ == '__main__':
    main()
