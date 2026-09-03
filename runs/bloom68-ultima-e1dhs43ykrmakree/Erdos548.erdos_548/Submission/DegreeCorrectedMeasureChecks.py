"""Exact checks for DegreeCorrectedMeasureFindings.md.

All weights are rational and embeddings are non-induced.  The finite searches
are audits, not proofs of the unproved critical-host inequality.  No Lean file
is imported or modified.  --geng adds exhaustive critical hosts of orders 8,9.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import math
import random
import subprocess
import time

import networkx as nx

SPEC_SHA = '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'


def falling(n, r):
    return math.prod(range(n-r+1, n+1)) if 0 <= r <= n else 0


def rooted_shape(T, v, parent=None):
    return tuple(sorted(rooted_shape(T, w, v) for w in T[v] if w != parent))


def shape(T):
    return min((rooted_shape(T, v) for v in T), key=lambda s: (-len(s), s))


class SquareZeroWeight:
    """Integer-scaled subset-polynomial DP, then one rational division."""
    def __init__(self, G):
        self.G = nx.convert_node_labels_to_integers(G)
        self.n = len(G)
        self.adj = [list(self.G[v]) for v in self.G]
        self.deg = [len(row) for row in self.adj]
        self.L = math.lcm(*(d for d in self.deg if d))
        self.q = [self.L // d if d else 0 for d in self.deg]
        self.cache, self.total_cache = {}, {}

    def polynomial(self, s, root=False):
        key = s, root
        if key in self.cache:
            return self.cache[key]
        power = len(s) - int(root)
        assert power >= 0  # single-vertex trees handled separately
        result = [{1 << v: self.q[v]**power} if self.deg[v] else {}
                  for v in range(self.n)]
        for child in s:
            child_polys = self.polynomial(child)
            merged = []
            for v in range(self.n):
                neigh = Counter()
                for w in self.adj[v]:
                    for mask, c in child_polys[w].items():
                        if not mask & (1 << v):
                            neigh[mask] += c
                row = Counter()
                for S, a in result[v].items():
                    for R, b in neigh.items():
                        if not S & R:
                            row[S | R] += a*b
                merged.append(dict(row))
            result = merged
        self.cache[key] = result
        return result

    def weight(self, T):
        if len(T) == 1:
            return Fraction(sum(self.deg))
        s = shape(T)
        if s not in self.total_cache:
            total = sum(sum(row.values()) for row in self.polynomial(s, True))
            self.total_cache[s] = Fraction(total, self.L**(len(T)-2))
        return self.total_cache[s]


def direct_weight(T, G, marked=None):
    """Independent injective backtracker, also measuring one-step escape."""
    G = nx.convert_node_labels_to_integers(G)
    n = len(G)
    deg = [G.degree(v) for v in G]
    L = math.lcm(*(d for d in deg if d))
    q = [L//d if d else 0 for d in deg]
    adj = [list(G[v]) for v in G]
    masks = [sum(1 << w for w in row) for row in adj]
    root = marked if marked is not None else max(T, key=T.degree)
    order, parents = [root], {root: None}
    for u in order:
        for w in T[u]:
            if w not in parents:
                parents[w] = u
                order.append(w)
    images = {}
    total = escape = 0

    def visit(i, occupied, weight):
        nonlocal total, escape
        if i == len(order):
            total += weight
            if marked is not None:
                v = images[marked]
                free = deg[v] - (masks[v] & occupied).bit_count()
                escape += weight * free * q[v]
            return
        u = order[i]
        choices = range(n) if parents[u] is None else adj[images[parents[u]]]
        for v in choices:
            if occupied & (1 << v) or deg[v] < T.degree(u):
                continue
            images[u] = v
            visit(i+1, occupied | (1 << v), weight*q[v]**(T.degree(u)-1))
            del images[u]

    visit(0, 0, 1)
    return (Fraction(total, L**(len(T)-2)),
            Fraction(escape, L**(len(T)-1)))


def ordinary_hom_weight(T, G):
    """No injectivity: ordinary scalar tree DP. Used only to check total 2m."""
    deg = dict(G.degree())
    root = max(T, key=T.degree)

    def rec(u, parent):
        rows = {v: Fraction(1, deg[v]**(T.degree(u)-1))
                for v in G if deg[v]}
        for w in T[u]:
            if w == parent:
                continue
            child = rec(w, u)
            rows = {v: value*sum(child.get(z, 0) for z in G[v])
                    for v, value in rows.items()}
        return rows

    return sum(rec(root, None).values())


def critical(G, k):
    n, m = len(G), G.number_of_edges()
    eps = 2*m - (k-1)*n
    if eps not in (1, 2):
        return False
    if any(2*G.degree(v) < k-1+eps for v in G):
        return False
    adj = [sum(1 << w for w in G[v]) for v in G]
    edges = [0]*(1 << n)
    for S in range(1, (1 << n)-1):
        bit = S & -S
        R, v = S-bit, bit.bit_length()-1
        edges[S] = edges[R] + (adj[v] & R).bit_count()
        if 2*edges[S] > (k-1)*S.bit_count():
            return False
    return True


def independent_joint(T, root=None):
    """(size, sum(deg_T(u)-1)) counts, separately root-in / root-out."""
    def add(p, q):
        r = Counter(p)
        r.update(q)
        return dict(r)

    def multiply(p, q):
        r = Counter()
        for (i, j), c in p.items():
            for (x, y), d in q.items():
                r[i+x, j+y] += c*d
        return dict(r)

    def rec(v, parent):
        yes, no = {(1, T.degree(v)-1): 1}, {(0, 0): 1}
        for w in T[v]:
            if w == parent:
                continue
            cy, cn = rec(w, v)
            yes = multiply(yes, cn)
            no = multiply(no, add(cy, cn))
        return yes, no

    return rec(next(iter(T)) if root is None else root, None)


def split_row_weight(row, order, r, only_size=None):
    b, D = r*r+1, r*(r+1)
    total = Fraction(0)
    for (s, j), count in row.items():
        if only_size is not None and s != only_size:
            continue
        injections = count * falling(b, s) * falling(r, order-s)
        if injections:
            total += Fraction(injections, r**j * D**(order-2-j))
    return total


def split_weight(T, r):
    yes, no = independent_joint(T)
    return split_row_weight(yes, len(T), r) + split_row_weight(no, len(T), r)


def split_host(r):
    b = r*r+1
    G = nx.empty_graph(r+b)
    G.add_edges_from((i, j) for i in range(r) for j in range(i+1, r+b))
    return G


def subdivide(H):
    H = nx.convert_node_labels_to_integers(H)
    T = nx.empty_graph(len(H))
    for u, v in H.edges():
        w = len(T)
        T.add_edges_from([(u, w), (w, v)])
    return H, T


def cut_partition(H, root, q):
    def rec(v, parent):
        return math.prod(q + rec(w, v) for w in H[v] if w != parent)
    return rec(root, None)


def verify_independent_algorithms():
    count = identities = hom_checks = 0
    for G in nx.graph_atlas_g():
        if not 2 <= len(G) <= 5:
            continue
        C = SquareZeroWeight(G)
        for size in range(2, min(5, len(G))+1):
            for T in nx.nonisomorphic_trees(size):
                W, _ = direct_weight(T, G)
                assert W == C.weight(T)
                assert ordinary_hom_weight(T, G) == 2*G.number_of_edges()
                count += 1
                hom_checks += 1
                if size >= 3:
                    leaf = next(v for v in T if T.degree(v) == 1)
                    p = next(iter(T[leaf]))
                    U = T.copy()
                    U.remove_node(leaf)
                    _, escape = direct_weight(U, G, p)
                    assert escape == W
                    identities += 1
    # Direct comparisons to the separate independent-set DP, including n>k+1.
    extra = [(r, T) for r in (1, 2)
             for T in nx.nonisomorphic_trees(2*r+1)]
    extra += [(3, nx.path_graph(7)), (3, subdivide(nx.star_graph(3))[1])]
    for r, T in extra:
        G = split_host(r)
        W, _ = direct_weight(T, G)
        assert W == split_weight(T, r)
        count += 1
    print('Independent backtracking/subset or split-DP comparisons:', count)
    print('Direct weighted leaf identities:', identities)
    print('Unconditioned hom-weight identities:', hom_checks)


def verify_split_theorems():
    subset_types = coefficient_checks = tree_checks = leaf_checks = strong_checks = 0
    for r in range(1, 61):
        b, n = r*r+1, r*r+r+1
        m = r*(r-1)//2 + r*b
        assert 2*m == (2*r-1)*n+1
        for x in range(r+1):
            for y in range(b+1):
                if (x, y) == (r, b):
                    continue
                assert x*(x-1)+2*x*y <= (2*r-1)*(x+y)
                subset_types += 1
    for r in range(2, 301):
        B = r*r-r+1
        for t in range(r):
            assert math.comb(B, t) >= (r+1)**t
            coefficient_checks += 1
    for r in range(1, 8):
        q = Fraction(1, r+1)
        b, D = r*r+1, r*(r+1)
        beta = Fraction(b-r, D)
        base = Fraction(math.factorial(r)*falling(b, r), D**(r-1)*r**(r-1))
        M = (1+q)**(2*r-1)
        perfect_cache = {}
        for T in nx.nonisomorphic_trees(2*r+1):
            W = split_weight(T, r)
            tree_checks += 1
            for leaf in T:
                if T.degree(leaf) != 1:
                    continue
                p = next(iter(T[leaf]))
                U = T.copy()
                U.remove_node(leaf)
                yes, no = independent_joint(U, p)
                yes_weight = split_row_weight(yes, len(U), r)
                no_weight = split_row_weight(no, len(U), r)
                Z = yes_weight+no_weight
                blocked = split_row_weight(yes, len(U), r, only_size=r)
                good = Z-blocked
                assert blocked <= base*M
                assert good >= base
                # Independent exact one-step computation from the class patterns.
                extension = beta*no_weight
                for (s, j), c in yes.items():
                    if s >= r:
                        extension += split_row_weight({(s, j): c}, len(U), r)*Fraction(s-r, r)
                assert extension == W
                m = r*(r-1)//2+r*b
                assert 2*m*W >= Z
                if r >= 2:
                    assert r*(1+M)*W >= Z
                    assert 10*r*W > Z
                key = shape(U)
                if key not in perfect_cache:
                    perfect_cache[key] = len(nx.max_weight_matching(U, maxcardinality=True)) == r
                if perfect_cache[key]:
                    Mp = (1+q)**(r-1)
                    assert base <= blocked <= base*Mp
                    assert base <= good <= base*Mp
                    assert W == beta*good
                    assert (1+Mp)*W >= beta*Z
                    assert 8*W > Z
                    strong_checks += 1
                leaf_checks += 1
        print('Split exact tree/leaf tests through r=', r, ':', tree_checks, leaf_checks, flush=True)
    print('Critical proper-subset types:', subset_types)
    print('Coefficient monotonicity checks:', coefficient_checks)
    print('Perfect-matching strengthened leaf checks:', strong_checks)


def verify_subdivision_formula():
    trees = leaves = 0
    for order in range(2, 11):
        for H0 in nx.nonisomorphic_trees(order):
            H, T = subdivide(H0)
            r = H.number_of_edges()
            q, beta = Fraction(1, r+1), Fraction(r*r-r+1, r*(r+1))
            W = split_weight(T, r)
            for leaf in H:
                if H.degree(leaf) != 1:
                    continue
                p = next(iter(H[leaf]))
                R, U = H.copy(), T.copy()
                R.remove_node(leaf)
                U.remove_node(leaf)
                assert W / split_weight(U, r) == beta/(1+cut_partition(R, p, q))
                leaves += 1
            trees += 1
    H = nx.path_graph(20)
    for v in range(20):
        for _ in range(2 if v in (0, 19) else 1):
            H.add_edge(v, len(H))
    H, T = subdivide(H)
    r, n = 41, 1723
    assert len(T) == 83 and max(dict(T.degree()).values()) == 3
    W = split_weight(T, r)
    ratios = []
    for leaf in H:
        if H.degree(leaf) != 1:
            continue
        p = next(iter(H[leaf]))
        R, U = H.copy(), T.copy()
        R.remove_node(leaf)
        U.remove_node(leaf)
        count = 1+cut_partition(R, p, 1)
        assert n*(r*r+1-r) < count  # uniform recurrence fails
        ratio = W / split_weight(U, r)
        exact = Fraction(r*r-r+1, r*(r+1))/(1+cut_partition(R, p, Fraction(1, r+1)))
        assert ratio == exact and ratio > Fraction(1, 8)
        ratios.append(ratio)
    assert len(ratios) == 22
    print('Subdivision cut-formula checks:', trees, 'tree types;', leaves, 'leaves')
    print('82-edge counterexample: all 22 weighted ratios >1/8; range',
          float(min(ratios)), float(max(ratios)))


def verify_average_only_obstruction():
    k, c, M = 10, 100, 50
    n, m = c*(k+1)+M+1, c*k*(k+1)//2+M
    eps = 2*m-(k-1)*n
    A = Fraction(math.factorial(k+1), k**(k-2))
    B = Fraction(falling(M, k-1), M**(k-2))
    ZU, ZT = c*A+B, c*A/k
    assert (n, m, eps) == (1151, 5550, 741)
    deficit = 2*m*ZT-eps*ZU
    assert deficit == -Fraction(3072907492578, 1220703125)
    assert 2*math.comb(11, 2) > (k-1)*11  # a proper dense induced clique
    print('Average-only weighted inequality FAILS, exact signed difference:', deficit)


def scan_critical_hosts(use_geng):
    host_checks = tree_checks = leaf_checks = 0
    worst = None

    def check(G, k):
        nonlocal host_checks, tree_checks, leaf_checks, worst
        if not critical(G, k):
            return
        host_checks += 1
        m = G.number_of_edges()
        eps = 2*m-(k-1)*len(G)
        C = SquareZeroWeight(G)
        for T in nx.nonisomorphic_trees(k+1):
            W = C.weight(T)
            tree_checks += 1
            for leaf in T:
                if T.degree(leaf) != 1:
                    continue
                U = T.copy()
                U.remove_node(leaf)
                Z = C.weight(U)
                assert Z > 0
                ratio = 2*m*W/(eps*Z)
                assert ratio >= 1, (list(G.edges()), list(T.edges()), leaf, ratio)
                worst = ratio if worst is None else min(worst, ratio)
                leaf_checks += 1

    for G in nx.graph_atlas_g():
        for k in range(2, len(G)):
            check(G, k)
    print('Critical atlas: hosts, trees, leaves, worst ratio:',
          host_checks, tree_checks, leaf_checks, worst, flush=True)
    if use_geng:
        for n in (8, 9):
            for k in range(3, n):
                m = (k-1)*n//2+1
                eps = 2*m-(k-1)*n
                delta = (k-1+eps+1)//2
                proc = subprocess.Popen(['nauty-geng', '-q', f'-d{delta}', str(n), f'{m}:{m}'],
                                        stdout=subprocess.PIPE)
                for line in proc.stdout:
                    check(nx.from_graph6_bytes(line.strip()), k)
                assert proc.wait() == 0
                print('Critical search through n,k =', n, k, ':',
                      host_checks, tree_checks, leaf_checks, flush=True)
    print('Finite critical-host candidate audit PASSED:', host_checks, tree_checks, leaf_checks)
    print('This finite audit is NOT a proof of the general critical-host inequality.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--geng', action='store_true')
    args = parser.parse_args()
    start = time.time()
    spec = Path(__file__).with_name('Spec.lean')
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA
    verify_independent_algorithms()
    verify_split_theorems()
    verify_subdivision_formula()
    verify_average_only_obstruction()
    scan_critical_hosts(args.geng)
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA
    print('Spec.lean unchanged:', SPEC_SHA)
    print('ALL CHECKS PASSED; seconds:', round(time.time()-start, 3))


if __name__ == '__main__':
    main()
