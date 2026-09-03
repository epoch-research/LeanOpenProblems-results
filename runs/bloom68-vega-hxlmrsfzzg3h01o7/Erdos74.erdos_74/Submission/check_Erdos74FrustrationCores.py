#!/usr/bin/env python3
"""Finite consistency checks for Erdos74FrustrationCores.md.

Requires NetworkX and NumPy; --milp additionally uses SciPy. All maximum-cut
checks enumerate every cut, fixing one vertex on one side. The general proofs
are in the companion note.
"""

from itertools import combinations
from math import comb, gcd
from functools import reduce

import networkx as nx
import numpy as np


def exact_cuts(G):
    """Return tau, criticality, optimum cut masks, vertices, edges.

    Edge attribute 'weight' is a positive integer multiplicity. Criticality
    means every edge class is bad in at least one optimum; then every labelled
    parallel copy is frustration-critical as well.
    """
    vs = list(G)
    pos = {v: i for i, v in enumerate(vs)}
    es = list(G.edges)
    bits = np.arange(1 << max(0, len(vs) - 1), dtype=np.uint64)
    costs = np.zeros(len(bits), dtype=np.int32)
    for u, v in es:
        bad = (((bits >> pos[u]) ^ (bits >> pos[v])) & 1) == 0
        costs += int(G[u][v].get("weight", 1)) * bad
    tau = int(costs.min())
    opts = bits[costs == tau]
    covered = []
    for u, v in es:
        covered.append(bool(np.any((((opts >> pos[u]) ^ (opts >> pos[v])) & 1) == 0)))
    return tau, all(covered), opts, vs, es


def modular_rank(A, prime=1000003):
    """Exact row rank over F_prime (integer arithmetic, not floating point)."""
    A = np.asarray(A, dtype=np.int64).copy() % prime
    row = 0
    for col in range(A.shape[1]):
        pivots = np.flatnonzero(A[row:, col])
        if len(pivots) == 0:
            continue
        pivot = row + int(pivots[0])
        A[[row, pivot]] = A[[pivot, row]]
        inv = pow(int(A[row, col]), -1, prime)
        A[row] = (A[row] * inv) % prime
        below = np.flatnonzero(A[row + 1:, col]) + row + 1
        if len(below):
            factors = A[below, col].copy()
            A[below] = (A[below] - factors[:, None] * A[row][None, :]) % prime
        row += 1
        if row == A.shape[0]:
            break
    return row


def weighted_base(a):
    q = 2 * a + 3
    G = nx.complete_graph(q + 2)
    weights = [a, a] + [1] * q
    for u, v in G.edges:
        G[u][v]["weight"] = weights[u] * weights[v]
    return G


def check_base(a):
    G = weighted_base(a)
    t, critical, opts, vs, es = exact_cuts(G)
    expected = 3 * a * a + 5 * a + 1
    assert t == expected and critical
    w = np.array([G[u][v]["weight"] for u, v in es], dtype=np.int64)
    assert int(w.sum()) == 7 * a * a + 11 * a + 3
    pos = {v: i for i, v in enumerate(vs)}
    B = np.array([((((opts >> pos[u]) ^ (opts >> pos[v])) & 1) == 0)
                  for u, v in es], dtype=np.int64).T
    A = B - B[0]
    assert np.all(A @ w == 0)
    rank = modular_rank(A)
    # Since w is a nonzero rational null vector, rank >= m-1 modulo a prime
    # and rank <= m-1 over Q prove exact rational rank m-1.
    assert rank == len(es) - 1
    assert reduce(gcd, map(int, w)) == 1
    # In any additive decomposition, each piece must satisfy A*x=0.
    # The one-dimensional kernel forces x=lambda*w, while unit edges force
    # lambda to be an integer in [0,1]. This corroborates indecomposability.
    print(f"base a={a}: tau={t}; {len(opts)} optimal cuts; every edge critical; "
          f"exact-rank certificate {rank}/{len(es)}; primitive weights", flush=True)


def strip_graph(a, L):
    assert a >= 2 and L >= 2 and L % 2 == 0
    q = 2 * a + 3
    G = nx.Graph()
    U = [("U", i) for i in range(q)]
    layers = [[("A", j, i) for i in range(a)] for j in range(L + 2)]
    G.add_nodes_from(U)
    for layer in layers:
        G.add_nodes_from(layer)
    G.add_edges_from(combinations(U, 2))
    for u in U:
        for v in layers[0] + layers[-1]:
            G.add_edge(u, v)
    for left, right in zip(layers, layers[1:]):
        for u in left:
            for v in right:
                G.add_edge(u, v)
    return G, U, layers


def check_strip(a, L, milp_check=False):
    G, U, layers = strip_graph(a, L)
    q = 2 * a + 3
    t, critical, opts, _, _ = exact_cuts(G)
    assert len(G) == a * L + 4 * a + 3
    assert G.number_of_edges() == a * a * L + 7 * a * a + 11 * a + 3
    assert t == 3 * a * a + 5 * a + 1 and critical
    assert min(dict(G.degree()).values()) == 2 * a
    for u in U:
        assert G.degree(u) == 4 * a + 2
    for u in layers[0] + layers[-1]:
        assert G.degree(u) == 3 * a + 3
    colour = {u: i for i, u in enumerate(U)}
    for j, layer in enumerate(layers):
        for v in layer:
            colour[v] = q if j in [0, L + 1] else j % 2
    assert all(colour[u] != colour[v] for u, v in G.edges)
    clique = U + [layers[0][0]]
    assert all(G.has_edge(u, v) for u, v in combinations(clique, 2))
    core = G.subgraph(U + layers[0] + layers[-1]).copy()
    core_t, core_critical, _, _, _ = exact_cuts(core)
    assert core_t == 2 * a * a + 5 * a + 1
    assert core_critical
    print(f"strip a={a}, L={L}: n={len(G)}, m={G.number_of_edges()}, tau={t}, "
          f"chi={q + 1}, delta={2 * a}; all {G.number_of_edges()} edges critical; "
          f"{len(opts)} optimum cuts; small core n={len(core)}, tau={core_t}", flush=True)
    if milp_check:
        from scipy.optimize import milp, Bounds, LinearConstraint
        vs, es = list(G), list(G.edges)
        pos = {v: i for i, v in enumerate(vs)}
        B = np.array([((((opts >> pos[u]) ^ (opts >> pos[v])) & 1) == 0)
                      for u, v in es], dtype=np.int64).T
        A = B - B[0]
        # In an additive decomposition, every optimum cut of G is optimum
        # on both parts. Hence its binary edge indicator x must satisfy
        # A*x=0 and 1 <= B[0]*x <= tau(G)-1. Infeasibility of these merely
        # necessary conditions corroborates the general proof in the note.
        constraints = LinearConstraint(
            np.r_[A, B[0][None, :]],
            np.r_[np.zeros(len(A)), 1],
            np.r_[np.zeros(len(A)), t - 1])
        result = milp(np.zeros(len(es)), integrality=np.ones(len(es)),
                      bounds=Bounds(np.zeros(len(es)), np.ones(len(es))),
                      constraints=constraints, options={"time_limit": 120})
        assert result.status == 2, result.message
        print(f"  direct indecomposability check: necessary binary additive-"
              f"partition system infeasible (HiGHS); optimum-row rank "
              f"{modular_rank(A)}/{len(es)}", flush=True)


def mycielski_triangle():
    G = nx.Graph()
    G.add_nodes_from(range(7))
    G.add_edges_from(combinations(range(3), 2))
    for i in range(3):
        for j in range(3):
            if i != j:
                G.add_edge(3 + i, j)
        G.add_edge(6, 3 + i)
    return G


def check_mycielski():
    G = mycielski_triangle()
    colour = {i: i for i in range(3)}
    colour.update({i + 3: i for i in range(3)})
    colour[6] = 3
    assert all(colour[u] != colour[v] for u, v in G.edges)
    # Exhaustive q-colour search, no symmetry pruning needed at order seven.
    def colourable(k):
        order = sorted(G, key=G.degree, reverse=True)
        chosen = {}
        def go(i):
            if i == len(order):
                return True
            v = order[i]
            bad = {chosen[w] for w in G[v] if w in chosen}
            for c in range(k):
                if c not in bad:
                    chosen[v] = c
                    if go(i + 1):
                        return True
                    del chosen[v]
            return False
        return go(0)
    assert not colourable(3) and colourable(4)
    es = list(G.edges)
    eligible = []
    for mask in range(1 << len(es)):
        H = nx.Graph(e for i, e in enumerate(es) if mask >> i & 1)
        if not H or min(dict(H.degree()).values()) < 3:
            continue
        t, critical, _, _, _ = exact_cuts(H)
        assert not critical
        assert set(H) == set(G)
        base_edges = sum(H.has_edge(u, v) for u, v in combinations(range(3), 2))
        assert base_edges in [2, 3] and t == base_edges
        for shadow in range(3, 6):
            K = H.copy()
            K.remove_edge(6, shadow)
            assert exact_cuts(K)[0] == t
        eligible.append(H)
    assert len(eligible) == 4
    print("M(K3): chi=4; all 4096 edge subsets checked; exactly four "
          "minimum-degree-three subgraphs, none frustration-critical", flush=True)


def triangle_extension(J):
    H = J.copy()
    next_id = max(J) + 1
    private = {}
    for u, v in J.edges:
        private[(u, v)] = next_id
        H.add_edge(u, next_id)
        H.add_edge(v, next_id)
        next_id += 1
    return H, private


def check_factor_two():
    J = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
    J.add_edge(0, 3)
    H, private = triangle_extension(J)
    c = {0: 0, 1: 1, 2: 2, 3: 1, 4: 2, 5: 0}
    p = {v: int(v >= 3) for v in J}
    for (u, v), w in private.items():
        c[w] = next(i for i in range(3) if i not in [c[u], c[v]])
        p[w] = 1 - p[u] if p[u] == p[v] else 0
    assert all(c[u] != c[v] for u, v in H.edges)
    assert sum(p[u] == p[v] for u, v in H.edges) == J.number_of_edges()
    G = H.copy()
    for u, v in combinations(G, 2):
        if p[u] != p[v]:
            G.add_edge(u, v)
    th, ch, _, _, _ = exact_cuts(H)
    tg, _, _, _, _ = exact_cuts(G)
    assert th == tg == 7 and ch
    assert all(G.has_edge(u, v) for u, v in combinations(range(6), 2))
    six_colour = {v: 3 * p[v] + c[v] for v in G}
    assert all(six_colour[u] != six_colour[v] for u, v in G.edges)
    assert nx.is_connected(H)
    print(f"sharp factor two: connected critical H has n={len(H)}, tau=7, chi=3; "
          f"G has n={len(G)}, tau=7, chi=6, and contains K6", flush=True)


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--milp", action="store_true",
                        help="also test indecomposability directly using SciPy/HiGHS")
    args = parser.parse_args()
    for a in [2, 3, 4]:
        check_base(a)
    for a, L in [(2, 2), (2, 4), (3, 2)]:
        check_strip(a, L, milp_check=args.milp)
    check_mycielski()
    check_factor_two()
    print("All checks passed. These checks do not settle Erdos 74.", flush=True)


if __name__ == "__main__":
    main()
