#!/usr/bin/env python3
"""Constructive audit of the common-list, one-mark-per-component forest theorem.

This is an implementation of the proof in CommonMarkedForestCL.md, not a
backtracking solver and not a substitute for the mathematical proof.  Every
recursive call checks its degree/list hypotheses, every return is independently
checked as a marked injective homomorphism, and the root-sensitive degree
bounds are asserted when the final reembedding branch is reached.

Usage: python3 Submission/CommonMarkedForestChecks.py [--random N]
No imports from Submission.Spec and no changes to any Lean file.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import itertools as it
import random
import time

import networkx as nx


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def mask_of(vertices):
    ans = 0
    for v in vertices:
        ans |= 1 << v
    return ans


def first(mask):
    assert mask
    return (mask & -mask).bit_length() - 1


def take(mask, n):
    assert mask.bit_count() >= n
    return mask_of(it.islice(bits(mask), n))


def host_adjacency(H):
    assert set(H) == set(range(len(H)))
    return tuple(mask_of(H[v]) for v in range(len(H)))


@dataclass
class RootedTree:
    root: int
    order: tuple
    parent: dict
    neighbors: dict

    @property
    def edges(self):
        return len(self.order) - 1

    @property
    def root_star(self):
        return len(self.neighbors[self.root]) == self.edges


def compile_components(F, marks):
    marks = set(marks)
    assert marks <= set(F)
    if not F:
        assert not marks
        return []
    assert nx.is_forest(F)
    components = []
    for C in nx.connected_components(F):
        roots = C & marks
        assert len(roots) == 1
        root = next(iter(roots))
        parent = {root: None}
        order = [root]
        for v in order:
            for w in sorted(F[v]):
                if w != parent[v]:
                    assert w not in parent
                    parent[w] = v
                    order.append(w)
        assert set(order) == C
        components.append(RootedTree(root, tuple(order), parent,
                                     {v: tuple(F[v]) for v in C}))
    return components


def verify(adj, universe, allowed, components, phi):
    vertices = {v for C in components for v in C.order}
    assert set(phi) == vertices
    assert len(set(phi.values())) == len(phi)
    assert mask_of(phi.values()) & ~universe == 0
    for C in components:
        assert (allowed >> phi[C.root]) & 1
        for v in C.order:
            if C.parent[v] is not None:
                assert (adj[phi[v]] >> phi[C.parent[v]]) & 1
    return phi


def grow_tree(adj, universe, C, partial):
    """Greedily extend a connected rooted subtree; callers prove it cannot fail."""
    phi = dict(partial)
    assert C.root in phi
    used = mask_of(phi.values())
    assert len(phi) == used.bit_count()
    for v in C.order:
        if v in phi:
            continue
        assert C.parent[v] in phi
        options = adj[phi[C.parent[v]]] & universe & ~used
        assert options, ("greedy extension failed", C, partial, universe, phi, v)
        w = first(options)
        phi[v] = w
        used |= 1 << w
    return phi


def common_marked_forest(adj, universe, allowed, components, stats=None):
    """The proof as an algorithm. Components have disjoint target vertex sets."""
    if stats is None:
        stats = Counter()
    stats["calls"] += 1
    m = sum(len(C.order) for C in components)
    e = sum(C.edges for C in components)
    assert allowed & ~universe == 0
    assert allowed.bit_count() >= m
    assert all((adj[v] & universe).bit_count() >= e for v in bits(universe))

    def finish(phi):
        return verify(adj, universe, allowed, components, phi)

    isolated = [C for C in components if C.edges == 0]
    if isolated:
        stats["isolates_removed"] += len(isolated)
        nontrivial = [C for C in components if C.edges > 0]
        phi = common_marked_forest(adj, universe, allowed, nontrivial, stats)
        available = allowed & ~mask_of(phi.values())
        for C in isolated:
            w = first(available)
            phi[C.root] = w
            available &= ~(1 << w)
        return finish(phi)
    if not components:
        return finish({})
    if len(components) == 1:
        stats["single_tree"] += 1
        C = components[0]
        return finish(grow_tree(adj, universe, C, {C.root: first(allowed)}))

    p = len(components)
    # The size ordering of the original unmarked proof is not required.
    C1 = next((C for C in components if C.root_star), components[0])
    rest = [C for C in components if C is not C1]
    a = C1.edges
    seed = first(allowed)
    K = 1 << seed

    # Under failure, every A-rooted copy of C1 has an outside common neighbor.
    # Construct only the a-clique actually needed; if that implication fails,
    # induction directly supplies the desired forest embedding.
    while K.bit_count() < a:
        kv = [seed] + [v for v in bits(K) if v != seed]
        initial = dict(zip(C1.order[:len(kv)], kv))
        trial = grow_tree(adj, universe, C1, initial)
        image = mask_of(trial.values())
        universal = universe & ~image
        for v in trial.values():
            universal &= adj[v]
        if not universal:
            stats["clique_escape"] += 1
            other = common_marked_forest(adj, universe & ~image,
                                          allowed & ~image, rest, stats)
            return finish(trial | other)
        K |= 1 << first(universal)
        stats["clique_grow"] += 1
    assert K.bit_count() == a
    assert all((adj[v] & K).bit_count() == a - 1 for v in bits(K))

    leaf = next(v for v in C1.order if v != C1.root and
                len(C1.neighbors[v]) == 1)
    kv = [seed] + [v for v in bits(K) if v != seed]
    core = dict(zip((v for v in C1.order if v != leaf), kv))
    x = core[C1.parent[leaf]]
    X = take(adj[x] & universe & ~K, e - a + 1)
    g = common_marked_forest(adj, universe & ~K, allowed & ~K, rest, stats)
    occupied = mask_of(g.values())

    def complete_on_reserved_clique(other, z):
        assert (X >> z) & 1
        assert z not in other.values()
        return finish(other | core | {leaf: z})

    free_x = X & ~occupied
    if free_x:
        stats["reserved_leaf"] += 1
        return complete_on_reserved_clique(g, first(free_x))

    Y = occupied & ~X
    assert Y.bit_count() == p - 2
    S = universe & ~(K | occupied)
    s0 = first(S & allowed)
    free = K | S
    assert free == (universe & ~occupied)
    classes = {j: [] for j in range(1, 5)}
    for C in rest:
        image = mask_of(g[v] for v in C.order)
        nx_ = (image & X).bit_count()
        category = (1 if nx_ == len(C.order) else
                    2 if nx_ >= 2 else 3 if nx_ == 1 else 4)
        classes[category].append((C, image))
    q = {j: len(classes[j]) for j in classes}
    assert sum(q.values()) == p - 1
    rhs = (1 + sum(C.edges - 1 for C, _ in classes[3]) +
           sum(C.edges for C, _ in classes[4]))
    assert q[1] >= rhs >= 1 + q[4]

    # A legal one-vertex switch freeing any member of X completes the forest.
    inv_x = [(C, v, g[v]) for C in rest for v in C.order if (X >> g[v]) & 1]
    candidates = [s0] if C1.root_star else list(bits(S))
    for s in candidates:
        for C, v, old in inv_x:
            if v == C.root and not ((allowed >> s) & 1):
                continue
            if all((adj[s] >> g[w]) & 1 for w in C.neighbors[v]):
                other = dict(g)
                other[v] = s
                stats["switch_mark" if v == C.root else "switch_nonmark"] += 1
                stats["switch_into_A" if (allowed >> s) & 1 else
                      "switch_outside_A"] += 1
                return complete_on_reserved_clique(other, old)

    if C1.root_star:
        # At an unused A vertex, switches may move any component's mark.
        for C, image in classes[1]:
            assert (image & ~adj[s0]).bit_count() >= 2
        for j in (2, 3):
            for C, image in classes[j]:
                assert image & ~adj[s0]
        assert (adj[s0] & free).bit_count() >= a + q[1] - q[4] >= a + 1
        stats["star_finish"] += 1
        return finish(g | grow_tree(adj, free, C1, {C1.root: s0}))

    # If no marked-center star exists, its nonexistence repairs the lost swaps.
    assert all(not C.root_star and C.edges >= 2 for C in components)
    assert q[1] >= 1 + q[3] + 2*q[4]
    for s in bits(S):
        for C, image in classes[1]:
            assert (image & ~adj[s]).bit_count() >= 2
        for C, image in classes[2]:
            assert image & ~adj[s]
        assert ((adj[s] & free).bit_count() >=
                a + q[1] - q[3] - q[4] >= a + 1)
    stats["nonstar_finish"] += 1
    # Vertices of S have free degree >= a; a vertex of K always has a fresh
    # clique neighbor while the partial tree contains s0 and has <= a vertices.
    return finish(g | grow_tree(adj, free, C1, {C1.root: s0}))


def rooted_code(F, v, parent=None):
    return tuple(sorted(rooted_code(F, w, v) for w in F[v] if w != parent))


def marked_atlas_forests(atlas):
    ans = {n: [] for n in range(2, 8)}
    for F in atlas:
        if len(F) < 2 or not nx.is_forest(F):
            continue
        cc = list(nx.connected_components(F))
        if len(cc) < 2:
            continue
        choices = []
        for C in cc:
            representatives = {rooted_code(F, v): v for v in C}
            choices.append(tuple(representatives.values()))
        seen = set()
        for roots in it.product(*choices):
            code = tuple(sorted(rooted_code(F, r) for r in roots))
            if code not in seen:
                seen.add(code)
                ans[len(F)].append(compile_components(F, roots))
    return ans


def check_atlas(atlas, stats):
    forests = marked_atlas_forests(atlas)
    count = 0
    for H in atlas:
        n = len(H)
        if n < 3:
            continue
        adj = host_adjacency(H)
        universe = (1 << n) - 1
        delta = min(map(int.bit_count, adj))
        for m in range(2, n + 1):
            for comps in forests[m]:
                if sum(C.edges for C in comps) > delta:
                    continue
                for A in it.combinations(range(n), m):
                    common_marked_forest(adj, universe, mask_of(A), comps, stats)
                    count += 1
    assert count == 362970  # same domain as the earlier backtracking search
    return count


def check_local_switches(max_order=10):
    """All rooted trees through order 10 and all hypothetical adjacencies of s."""
    count = 0
    for n in range(2, max_order + 1):
        for T in nx.nonisomorphic_trees(n):
            representatives = {rooted_code(T, r): r for r in T}
            neighbors = {v: mask_of(T[v]) for v in T}
            allv = (1 << n) - 1
            for r in representatives.values():
                nonstar = T.degree(r) != n - 1
                for B in range(1 << n):
                    viable = mask_of(v for v in T if neighbors[v] & ~B == 0)
                    for in_A in (False, True):
                        eligible = viable if in_A else viable & ~(1 << r)
                        missing = n - B.bit_count()
                        if missing <= 1 and (in_A or nonstar):
                            assert eligible  # the all-X two-nonneighbor bound
                        if missing == 0:
                            assert eligible.bit_count() >= n - (not in_A)
                        # For a mixed class with >=2 X vertices, a completely
                        # adjacent s always permits a nonmarked replacement.
                        if missing == 0:
                            for pair in it.combinations(T, 2):
                                assert eligible & mask_of(pair)
                        count += 1
    return count


def check_clique_greedy(atlas):
    """Audit the final clique-plus-S extension lemma, using its weaker bound a."""
    trees = {}
    for a in range(1, 7):
        trees[a] = []
        for T in nx.nonisomorphic_trees(a + 1):
            for r in {rooted_code(T, v): v for v in T}.values():
                trees[a].append(compile_components(T, [r])[0])
    count = 0
    for H in atlas:
        n = len(H)
        adj = host_adjacency(H)
        universe = (1 << n) - 1
        for a in range(1, n):
            for vertices in it.combinations(range(n), a):
                K = mask_of(vertices)
                if not all((adj[v] & K).bit_count() == a - 1 for v in vertices):
                    continue
                S = universe & ~K
                if not all(adj[v].bit_count() >= a for v in bits(S)):
                    continue
                for s in bits(S):
                    for C in trees[a]:
                        phi = grow_tree(adj, universe, C, {C.root: s})
                        verify(adj, universe, 1 << s, [C], phi)
                        count += 1
    return count


def blowup(template, sizes, cliques):
    H = nx.Graph()
    parts = []
    for size, is_clique in zip(sizes, cliques):
        part = list(range(len(H), len(H) + size))
        H.add_nodes_from(part)
        parts.append(part)
        if is_clique:
            H.add_edges_from(it.combinations(part, 2))
    for u, v in template.edges():
        H.add_edges_from(it.product(parts[u], parts[v]))
    return H, parts


def check_random(atlas, iterations, stats):
    R = random.Random(20260829)
    templates = [H for H in atlas if 2 <= len(H) <= 6]
    count = 0
    for _ in range(iterations):
        template = R.choice(templates)
        sizes = [R.randint(1, 9) for _ in template]
        H, parts = blowup(template, sizes, [R.choice((False, True)) for _ in template])
        n = len(H)
        if n < 4:
            continue
        adj = host_adjacency(H)
        delta = min(map(int.bit_count, adj))
        A = sum((parts[i] for i in R.sample(range(len(parts)),
                 R.randint(1, len(parts)))), [])
        m = R.randint(3, min(n, 20))
        if len(A) < m:
            continue
        # Rooted forests from a deleted tree vertex cover arbitrary rooted
        # forest shapes: adjoining a new apex to their roots reverses this.
        T = nx.from_prufer_sequence([R.randrange(m + 1) for _ in range(m - 1)])
        roots = [u for u in T if T.degree(u) >= 2 and m - T.degree(u) <= delta]
        R.shuffle(roots)
        for u in roots[:3]:
            F = T.copy()
            marks = list(F[u])
            F.remove_node(u)
            common_marked_forest(adj, (1 << n) - 1, mask_of(A),
                                 compile_components(F, marks), stats)
            count += 1
    return count


def check_rooted_tree_corollary(atlas, stats):
    """All small instances of the exact local corollary, not only W_k hosts."""
    count = 0
    for H in atlas:
        n = len(H)
        if n < 2:
            continue
        adj = host_adjacency(H)
        universe = (1 << n) - 1
        for k in range(1, n):
            for T in nx.nonisomorphic_trees(k + 1):
                for u in T:
                    F = T.copy()
                    marks = list(F[u])
                    F.remove_node(u)
                    comps = compile_components(F, marks)
                    e = k - T.degree(u)
                    for s in H:
                        if H.degree(s) < k:
                            continue
                        remaining = universe & ~(1 << s)
                        if any((adj[v] & remaining).bit_count() < e for v in bits(remaining)):
                            continue
                        phi = common_marked_forest(adj, remaining, adj[s], comps, stats)
                        phi[u] = s
                        assert len(set(phi.values())) == k + 1
                        assert all((adj[phi[v]] >> phi[w]) & 1 for v, w in T.edges())
                        assert phi[u] == s
                        count += 1
    return count


def check_special_cases(stats):
    # Empty forest and isolated marked components, including empty host.
    common_marked_forest((), 0, 0, [], stats)
    H = nx.empty_graph(5)
    F = nx.empty_graph(5)
    common_marked_forest(host_adjacency(H), 31, 31, compile_components(F, range(5)), stats)
    # Force each of the final degree-counting branches: all X lies in one
    # host component and S lies in another, so no exchange is possible.
    for n in (2, 3):
        T = nx.path_graph(n)
        F = nx.disjoint_union(T, T)
        comps = compile_components(F, [0, n])
        e = 2 * (n - 1)
        H = nx.disjoint_union(nx.complete_graph(e + 1), nx.complete_graph(e + 1))
        allv = (1 << len(H)) - 1
        before = stats["star_finish" if n == 2 else "nonstar_finish"]
        common_marked_forest(host_adjacency(H), allv, allv, comps, stats)
        assert stats["star_finish" if n == 2 else "nonstar_finish"] > before
    # The |A| hypothesis cannot be lowered to |F|-1, even for two edges.
    H = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
    A = {0, 1, 2}
    F = nx.Graph([(0, 1), (2, 3)])
    marks = (0, 2)
    assert min(dict(H.degree()).values()) == F.number_of_edges() == 2
    assert len(A) == len(F) - 1
    assert not any(all(phi[r] in A for r in marks) and
                   all(H.has_edge(phi[v], phi[w]) for v, w in F.edges())
                   for image in it.permutations(H, len(F))
                   for phi in [dict(zip(F, image))])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--random", type=int, default=10000)
    args = parser.parse_args()
    start = time.time()
    atlas = nx.graph_atlas_g()
    stats = Counter()
    check_special_cases(stats)
    print("SPECIAL CASES PASS", flush=True)
    print("LOCAL SWITCHES PASS", check_local_switches(), flush=True)
    print("CLIQUE GREEDY PASS", check_clique_greedy(atlas), flush=True)
    print("CONSTRUCTIVE ATLAS CL PASS", check_atlas(atlas, stats), flush=True)
    print("ROOTED TREE LOCAL COROLLARY PASS", check_rooted_tree_corollary(atlas, stats), flush=True)
    print("CONSTRUCTIVE RANDOM CL PASS", args.random,
          check_random(atlas, args.random, stats), flush=True)
    print("PROOF BRANCH COUNTS", dict(sorted(stats.items())), flush=True)
    print("ALL CHECKS PASS; seconds", time.time() - start, flush=True)


if __name__ == "__main__":
    main()
