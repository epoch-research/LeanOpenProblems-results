"""Exact audits of the critical leaf-recurrence counterexamples.

This file does not modify or import any Lean specification.  Counts are
labelled injective homomorphisms, not induced copies.  The general proof is
in CriticalLeafRecurrenceCounterexample.md; finite checks are only audits.
"""
from collections import Counter
from functools import lru_cache
from fractions import Fraction
import argparse
import hashlib
import json
import math
from pathlib import Path
import time

import networkx as nx


def falling(x, t):
    if t < 0 or t > x:
        return 0
    return math.prod(range(x - t + 1, x + 1))


def add(p, q):
    r = Counter(p)
    r.update(q)
    return dict(r)


def multiply(p, q):
    r = Counter()
    for i, c in p.items():
        for j, d in q.items():
            r[i + j] += c * d
    return dict(r)


def independence_polynomial(T):
    """Independent-set size counts by an ordinary include/exclude tree DP."""
    def rec(v, parent):
        yes, no = {1: 1}, {0: 1}
        for w in T[v]:
            if w == parent:
                continue
            child_yes, child_no = rec(w, v)
            yes = multiply(yes, child_no)
            no = multiply(no, add(child_yes, child_no))
        return yes, no
    assert nx.is_tree(T)
    yes, no = rec(next(iter(T)), None)
    return add(yes, no)


def split_embedding_count(T, a, b):
    return sum(c * falling(b, s) * falling(a, len(T) - s)
               for s, c in independence_polynomial(T).items())


def subdivide(H):
    H = nx.convert_node_labels_to_integers(H)
    T = nx.Graph()
    T.add_nodes_from(H)
    edge_vertex = {}
    for i, (u, v) in enumerate(H.edges()):
        w = len(H) + i
        edge_vertex[frozenset((u, v))] = w
        T.add_edges_from([(u, w), (w, v)])
    assert nx.is_tree(T)
    return H, T, edge_vertex


def rooted_subtree_counts(H):
    """Counts connected vertex subsets containing a specified vertex."""
    @lru_cache(None)
    def branch(v, parent):
        return math.prod(1 + branch(w, v) for w in H[v] if w != parent)
    return {v: branch(v, None) for v in H}


def brute_rooted_subtree_counts(H):
    """Independent subset enumeration: in a forest e(S)=|S|-1 iff connected."""
    H = nx.convert_node_labels_to_integers(H)
    n = len(H)
    adj = [sum(1 << w for w in H[v]) for v in H]
    es = [0] * (1 << n)
    out = [0] * n
    for mask in range(1, 1 << n):
        bit = mask & -mask
        rest = mask - bit
        v = bit.bit_length() - 1
        es[mask] = es[rest] + (adj[v] & rest).bit_count()
        if es[mask] == mask.bit_count() - 1:
            for u in range(n):
                if mask & (1 << u):
                    out[u] += 1
    return dict(enumerate(out))


def split_host(a):
    b = a*a + 1
    G = nx.Graph()
    G.add_nodes_from(range(a + b))
    G.add_edges_from((i, j) for i in range(a) for j in range(i + 1, a))
    G.add_edges_from((i, j) for i in range(a) for j in range(a, a + b))
    return G


def direct_embedding_count(T, G, marked=None):
    """A separate injective backtracker, retaining rooted extension statistics."""
    root = marked if marked is not None else max(T, key=T.degree)
    order = [root]
    parent = {root: None}
    for v in order:
        for w in T[v]:
            if w not in parent:
                parent[w] = v
                order.append(w)
    f = {}
    used = set()
    totals = [0] * len(G)
    extensions = [0] * len(G)
    def rec(i):
        if i == len(order):
            v = f[root]
            totals[v] += 1
            extensions[v] += len(set(G[v]) - used)
            return
        u = order[i]
        candidates = G if parent[u] is None else G[f[parent[u]]]
        for v in candidates:
            if v in used or G.degree(v) < T.degree(u):
                continue
            f[u] = v
            used.add(v)
            rec(i + 1)
            used.remove(v)
            del f[u]
    rec(0)
    return sum(totals), totals, extensions


def caterpillar(spine_length):
    h = spine_length
    assert h >= 2
    H = nx.path_graph(h)
    leaves_by_parent = {}
    next_label = h
    for i in range(h):
        leaves_by_parent[i] = []
        for _ in range(2 if i in (0, h-1) else 1):
            H.add_edge(i, next_label)
            leaves_by_parent[i].append(next_label)
            next_label += 1
    assert H.number_of_edges() == 2*h + 1
    assert max(dict(H.degree()).values()) == 3
    return H, leaves_by_parent


def verify_critical_types(a):
    b = a*a + 1
    k = 2*a
    n = a + b
    m = a*(a-1)//2 + a*b
    assert n >= k + 1
    assert 2*m - (k-1)*n == 1
    checks = 0
    # Every induced set is specified, up to automorphism, by this pair.
    for x in range(a + 1):
        for y in range(b + 1):
            if (x, y) == (a, b):
                continue
            e = x*(x-1)//2 + x*y
            assert 2*e <= (k-1)*(x+y), (a, x, y)
            checks += 1
    return checks


def example(H, name):
    H, T, _ = subdivide(H)
    a = H.number_of_edges()
    b, n, k = a*a+1, a*a+a+1, 2*a
    G = split_host(a)
    assert len(G) == n
    assert 2*G.number_of_edges() - (k-1)*n == 1
    assert min(dict(G.degree()).values()) == a
    assert max(dict(G.degree()).values()) == n-1
    assert not nx.is_bipartite(G)
    # Explicit embedding: original H vertices in the independent part,
    # subdivision vertices in the clique.
    f = {v: a+v for v in H}
    f.update({v: v-len(H) for v in T if v not in H})
    assert len(set(f.values())) == len(T)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())
    leaf_R = rooted_subtree_counts(H)
    full = split_embedding_count(T, a, b)
    assert full == math.factorial(a)*falling(b, a+1)
    leaves = [v for v in H if H.degree(v) == 1]
    results = []
    for ell in leaves:
        U = T.copy()
        p = next(iter(T[ell]))
        U.remove_node(ell)
        coeff = independence_polynomial(U)
        assert max(coeff) == a
        assert coeff[a] == leaf_R[ell]
        partial = split_embedding_count(U, a, b)
        assert partial == leaf_R[ell]*math.factorial(a)*falling(b, a)
        assert n*full < partial, (name, ell, n*full, partial)
        assert T.degree(p) == 2
        # In a rooted leaf-deleted tree the special independent-set pattern
        # with no subdivision vertices is the sole extendible pattern.
        results.append({
            'leaf': ell,
            'rooted_subtrees': leaf_R[ell],
            'I_T_over_I_U': str(Fraction(b-a, leaf_R[ell])),
            'n_I_T_over_I_U': str(Fraction(n*(b-a), leaf_R[ell])),
        })
    # Literal +1 hypothesis can also be met by the disjoint union of two G's.
    union_n, union_m = 2*n, 2*G.number_of_edges()
    assert 2*union_m == (k-1)*union_n + 2
    return {
        'name': name, 'a': a, 'b': b, 'k': k, 'n': n,
        'm': G.number_of_edges(), 'epsilon': 1,
        'tree_max_degree': max(dict(T.degree()).values()),
        'tree_leaves': len(leaves),
        'min_rooted_subtrees': min(leaf_R[v] for v in leaves),
        'n_times_b_minus_a': n*(b-a),
        'all_leaf_inequalities_strictly_fail': True,
        'explicit_full_embedding_checked': True,
        'counts_via_independence_DP_checked': True,
        'I_T_digits': len(str(full)),
        'leaf_results': results,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', default='/tmp/es_leaf_transport/verified_counterexamples.json')
    args = parser.parse_args()
    start = time.time()
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    stats = {
        'critical_subset_types': 0,
        'subdivision_tree_cases': 0,
        'subdivision_leaf_cases': 0,
        'independent_subset_enumerations': 0,
        'direct_embedding_cases': 0,
        'direct_root_extension_checks': 0,
        'caterpillar_formula_leaf_cases': 0,
    }
    for a in range(1, 61):
        stats['critical_subset_types'] += verify_critical_types(a)
    for a in range(1, 10):
        for H in nx.nonisomorphic_trees(a+1):
            H, T, _ = subdivide(H)
            b = a*a+1
            R = rooted_subtree_counts(H)
            assert R == brute_rooted_subtree_counts(H)
            stats['independent_subset_enumerations'] += (1 << len(H))-1
            pt = independence_polynomial(T)
            assert max(pt) == a+1 and pt[a+1] == 1
            assert split_embedding_count(T, a, b) == math.factorial(a)*falling(b, a+1)
            stats['subdivision_tree_cases'] += 1
            if a <= 3:
                G = split_host(a)
                direct, _, _ = direct_embedding_count(T, G)
                assert direct == split_embedding_count(T, a, b)
                stats['direct_embedding_cases'] += 1
            for ell in H:
                if H.degree(ell) != 1:
                    continue
                U = T.copy()
                p = next(iter(T[ell]))
                U.remove_node(ell)
                pu = independence_polynomial(U)
                assert max(pu) == a and pu[a] == R[ell]
                assert split_embedding_count(U, a, b) == R[ell]*math.factorial(a)*falling(b, a)
                stats['subdivision_leaf_cases'] += 1
                if a <= 3:
                    direct, rooted, ext = direct_embedding_count(U, G, p)
                    assert direct == split_embedding_count(U, a, b)
                    assert sum(ext) == split_embedding_count(T, a, b)
                    for v in range(a):
                        assert rooted[v] == math.factorial(a-1)*falling(b, a)
                        assert ext[v] == (b-a)*rooted[v]
                    for v in range(a, a+b):
                        assert rooted[v] == (R[ell]-1)*math.factorial(a)*falling(b-1, a-1)
                        assert ext[v] == 0
                    stats['direct_embedding_cases'] += 1
                    stats['direct_root_extension_checks'] += len(G)
    for h in range(2, 61):
        H, groups = caterpillar(h)
        R = rooted_subtree_counts(H)
        for i, leaves in groups.items():
            if i in (0, h-1):
                expected = 3*(2**h)-1
            else:
                # Python index i corresponds to the mathematical v_(i+1).
                expected = 1 + (6*2**(i-1)-1)*(6*2**(h-i-2)-1)
            for ell in leaves:
                assert R[ell] == expected
                assert R[ell] >= 3*(2**h)-1
                stats['caterpillar_formula_leaf_cases'] += 1
    star_H = nx.star_graph(18)
    cat_H, _ = caterpillar(20)
    stats['counterexamples'] = [
        example(star_H, '36-edge once-subdivided star'),
        example(cat_H, '82-edge subcubic caterpillar subdivision'),
    ]
    # A second leaf-transitive subcubic example, independently shaped.
    H = nx.Graph()
    H.add_node(0)
    next_label = 1
    for _ in range(3):
        branch = nx.balanced_tree(2, 3)  # 15 vertices, 8 leaves
        mapping = {v: next_label+v for v in branch}
        H.update(nx.relabel_nodes(branch, mapping))
        H.add_edge(0, next_label)
        next_label += len(branch)
    third = example(H, '90-edge leaf-transitive subcubic subdivision')
    assert third['a'] == 45
    assert third['min_rooted_subtrees'] == 119165813
    assert len({r['rooted_subtrees'] for r in third['leaf_results']}) == 1
    stats['counterexamples'].append(third)
    after = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == after == '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'
    stats['spec_sha256_unchanged'] = after
    stats['elapsed_seconds'] = round(time.time()-start, 3)
    Path(args.output).parent.mkdir(parents=True, exist_ok=True)
    Path(args.output).write_text(json.dumps(stats, indent=2)+'\n')
    summary = {k: v for k, v in stats.items() if k != 'counterexamples'}
    print(json.dumps(summary, indent=2))
    for result in stats['counterexamples']:
        print(json.dumps({k: v for k, v in result.items() if k != 'leaf_results'}, indent=2))
    print('PASS; detailed output:', args.output)


if __name__ == '__main__':
    main()
