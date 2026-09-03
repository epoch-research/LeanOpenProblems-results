#!/usr/bin/env python3
"""Exact finite checks for ResearchRetirement.md (standard library only).

The general obstruction is proved in the Markdown file, not by enumeration.
No existing Submission file is edited, and no older checker is imported.
Run: python3 Submission/ResearchRetirementCheck.py
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import gcd, isqrt
from pathlib import Path
import json
import random

ROOT = Path(__file__).resolve().parent
SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"
NEW_FILES = {"ResearchRetirement.md", "ResearchRetirementCheck.py"}


def protected_hashes():
    return {p.name: sha256(p.read_bytes()).hexdigest()
            for p in ROOT.iterdir() if p.is_file() and p.name not in NEW_FILES}


def edge(u, v):
    assert u != v
    return (u, v) if u < v else (v, u)


def cycle_edges(C):
    assert len(C) >= 3 and len(set(C)) == len(C)
    return tuple(edge(C[i], C[(i+1) % len(C)]) for i in range(len(C)))


def assert_partition(vertices, edges, cycles):
    vertices = set(vertices)
    counts = Counter()
    for C in cycles:
        assert set(C) <= vertices
        counts.update(cycle_edges(C))
    assert set(counts) == set(edges)
    assert all(c == 1 for c in counts.values())


def cartesian_graph(m, t, complete):
    assert m >= 2 and t >= 1
    vertices = tuple(product(range(m), repeat=t))
    if complete:
        base = tuple(combinations(range(m), 2))
    else:
        assert m >= 3
        base = tuple(edge(i, (i+1) % m) for i in range(m))
    edges = set()
    for i in range(t):
        for background in product(range(m), repeat=t-1):
            for a, b in base:
                x, y = list(background), list(background)
                x.insert(i, a)
                y.insert(i, b)
                edges.add(edge(tuple(x), tuple(y)))
    assert len(edges) == t * len(base) * m**(t-1)
    return vertices, edges


def adjacency_masks(vertices, edges):
    ids = {v: i for i, v in enumerate(vertices)}
    adj = [0] * len(vertices)
    for u, v in edges:
        a, b = ids[u], ids[v]
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def induced_edges(mask, adj):
    answer = 0
    while mask:
        bit = mask & -mask
        i = bit.bit_length()-1
        mask ^= bit
        answer += (adj[i] & mask).bit_count()
    return answer


def induced_min_degree(mask, adj):
    remaining, values = mask, []
    while remaining:
        bit = remaining & -remaining
        i = bit.bit_length()-1
        remaining ^= bit
        values.append((adj[i] & mask).bit_count())
    return min(values)


def check_entropy_and_dense_order():
    rows = []
    rng = random.Random(1842026)
    cases = [(2, 4, None), (3, 2, F(2, 3)), (4, 2, F(1, 2)),
             (7, 1, F(1, 2)), (3, 3, F(2, 3)), (5, 2, F(1, 2))]
    for m, t, eta in cases:
        vertices, edges = cartesian_graph(m, t, True)
        n, D = len(vertices), t*(m-1)
        adj = adjacency_masks(vertices, edges)
        assert all(a.bit_count() == D for a in adj)
        tadj = None
        if m >= 3:
            tv, te = cartesian_graph(m, t, False)
            assert tv == vertices
            tadj = adjacency_masks(tv, te)
        exhaustive = n <= 16
        if exhaustive:
            masks = range(1, 1 << n)
        else:
            # Includes every coordinate clique and the full set, besides random subsets.
            selected = {(1 << n)-1}
            selected.update(rng.randrange(1, 1 << n) for _ in range(10000))
            for i in range(t):
                for background in product(range(m), repeat=t-1):
                    selected.add(sum(1 << j for j, v in enumerate(vertices)
                                     if v[:i]+v[i+1:] == background))
            masks = sorted(selected)
        maximum_share = F(0)
        dense_sets = tested = 0
        for mask in masks:
            s = mask.bit_count()
            e = induced_edges(mask, adj)
            # 2e <= (m-1)s log_m(s), with NO floating point logarithms.
            assert m**(2*e) <= s**((m-1)*s)
            if tadj is not None:
                et = induced_edges(mask, tadj)
                # e_T(X) <= |X| log_2 |X|, also checked by integers.
                assert 2**et <= s**s
            if eta is not None and 2*e >= eta*s*s:
                delta = induced_min_degree(mask, adj)
                if delta >= eta*s:
                    dense_sets += 1
                    assert m >= 2/eta
                    assert s < 2*m/eta
                    share = F(2*e, D*s)
                    maximum_share = max(maximum_share, share)
                    assert share <= F(2, t)
            tested += 1
        rows.append({"m": m, "t": t, "n": n, "subsets": tested,
                     "exhaustive": exhaustive, "eta": str(eta),
                     "dense_induced_sets": dense_sets,
                     "largest_observed_dense_average_share": str(maximum_share)})
    return rows


def check_coordinate_cliques():
    rows = []
    for m, t in [(3, 3), (5, 3), (7, 2), (9, 2)]:
        vertices, edges = cartesian_graph(m, t, True)
        incidence = Counter()
        orders = 0
        clique_count = 0
        for i in range(t):
            for background in product(range(m), repeat=t-1):
                Q = []
                for a in range(m):
                    v = list(background)
                    v.insert(i, a)
                    Q.append(tuple(v))
                incidence.update(edge(u, v) for u, v in combinations(Q, 2))
                orders += len(Q)
                clique_count += 1
                # Each clique spends exactly 1/t at each of its vertices.
                assert sum((F(m-1, t*(m-1)) for _ in Q), F()) == F(m, t)
        assert set(incidence) == edges
        assert all(v == 1 for v in incidence.values())
        assert orders == t*len(vertices)
        assert clique_count == t*m**(t-1)
        rows.append({"m": m, "t": t, "cliques": clique_count,
                     "sum_core_orders": orders, "n": len(vertices)})
    return rows


def walecki(m):
    assert m >= 3 and m % 2 == 1
    r, modulus = (m-1)//2, m-1
    result = []
    for a in range(r):
        C = [m-1, a]  # m-1 denotes infinity.
        for j in range(1, r):
            C += [(a-j) % modulus, (a+j) % modulus]
        C += [(a-r) % modulus]
        result.append(tuple(C))
    assert_partition(range(m), {edge(u, v) for u, v in combinations(range(m), 2)}, result)
    return tuple(result)


def two_hamilton_torus(M, m):
    assert M >= 3 and m >= 3 and M % m == 0 and gcd(M, m-1) == 1
    answer = []
    for colour in (0, 1):
        point, seen, C = (0, 0), set(), []
        while point not in seen:
            x, y = point
            seen.add(point)
            C.append(point)
            horizontal = ((x+y) % m != m-1) ^ bool(colour)
            point = ((x+1) % M, y) if horizontal else (x, (y+1) % m)
        assert point == (0, 0) and len(C) == M*m
        answer.append(tuple(C))
    # Independent full edge-set check, not just the orbit length calculation.
    vertices = tuple(product(range(M), range(m)))
    edges = {edge((x, y), ((x+1) % M, y)) for x, y in vertices}
    edges |= {edge((x, y), (x, (y+1) % m)) for x, y in vertices}
    assert_partition(vertices, edges, answer)
    return tuple(answer)


@lru_cache(None)
def cycle_power(m, t):
    assert m >= 3 and t >= 1
    if t == 1:
        return (tuple((a,) for a in range(m)),)
    old = cycle_power(m, t-1)
    H = old[0]
    assert len(H) == m**(t-1)
    result = [tuple(H[x]+(y,) for x, y in C)
              for C in two_hamilton_torus(len(H), m)]
    result += [tuple(v+(y,) for v in C) for C in old[1:] for y in range(m)]
    assert len(result) == (m**(t-1)+m-2)//(m-1)
    assert len(result[0]) == m**t
    return tuple(result)


def check_product_partitions():
    torus_rows, hamming_rows = [], []
    for m in range(3, 8):
        for t in range(1, 5):
            if m**t > 1600:
                continue
            vertices, edges = cartesian_graph(m, t, False)
            cycles = cycle_power(m, t)
            assert_partition(vertices, edges, cycles)
            q, n = len(cycles), len(vertices)
            assert q == (m**(t-1)+m-2)//(m-1)
            assert q <= F(n, m)
            if t >= 2:
                assert q <= F(2*n, m*m)
            torus_rows.append({"m": m, "t": t, "n": n, "cycles": q})
    cases = [(m, t) for m, top in [(3, 7), (5, 4), (7, 3), (9, 3), (11, 2)]
             for t in range(1, top+1)]
    for m, t in cases:
        vertices, edges = cartesian_graph(m, t, True)
        n, D = len(vertices), t*(m-1)
        cycles, share_sum = [], F()
        for B in walecki(m):
            packet_cycles = [tuple(tuple(B[a] for a in v) for v in C)
                             for C in cycle_power(m, t)]
            packet_edges = {e for C in packet_cycles for e in cycle_edges(C)}
            degree = Counter(v for e in packet_edges for v in e)
            assert set(degree) == set(vertices)
            assert all(d == 2*t for d in degree.values())
            W = sum((F(degree[v], D) for v in vertices), F())
            assert W == F(2*n, m-1)
            assert len(packet_cycles) <= W/2
            share_sum += W
            cycles.extend(packet_cycles)
        assert_partition(vertices, edges, cycles)
        assert share_sum == n
        assert len(cycles) == (m**(t-1)+m-2)//2
        assert len(cycles) <= F(n, 2)
        if t >= 2:
            assert len(cycles) <= F(n, m)
        old_count = t*m**(t-1)*(m-1)//2
        hamming_rows.append({"m": m, "t": t, "n": n,
                             "coordinate_local_cycles": old_count,
                             "reopened_partition_cycles": len(cycles),
                             "sum_original_degree_shares": str(share_sum)})
    return {"torus_partitions": torus_rows, "Hamming_partitions": hamming_rows}


def check_symbolic_obstruction():
    # An exact-parameter witness; its exponentially large graph is NOT built.
    m, t = 81, 65
    eta, alpha, gamma, B, C = F(1, 4), F(1, 8), 1, 5, 10
    sqrt_m = isqrt(m)
    assert sqrt_m**2 == m and m % 2 == 1
    assert m >= 2/eta
    assert F(2, t) < alpha
    n = m**t
    total_edges = t*n*(m-1)//2
    sparse_cap = gamma*t*n*sqrt_m  # epsilon=1/2
    # lambda <= 2 implies e(K) <= (m-1)|K| for every eta-dense K.
    normalized_order_lower = F(total_edges-sparse_cap-B*n, (m-1)*n)
    assert normalized_order_lower == F(201, 8) > C
    assert m*(m-1)//2 > gamma*m*sqrt_m
    repaired_count = (m**(t-1)+m-2)//2
    assert repaired_count <= F(n, 2)
    return {"graph": "K_81 Cartesian-power 65", "n": "81^65",
            "alpha": str(alpha), "eta": str(eta), "epsilon": "1/2",
            "gamma": gamma, "exception_edges_per_vertex": B,
            "forbidden_core_order_budget_per_vertex": C,
            "dense_core_average_share_upper": str(F(2, t)),
            "dense_core_total_order_over_n_lower": str(normalized_order_lower),
            "materialized": False}


def main():
    before = protected_hashes()
    assert before["Spec.lean"] == SPEC_SHA256
    result = {
        "entropy_and_dense_order": check_entropy_and_dense_order(),
        "coordinate_clique_ledger": check_coordinate_cliques(),
        "constructive_repairs": check_product_partitions(),
        "symbolic_obstruction": check_symbolic_obstruction(),
    }
    assert protected_hashes() == before
    result["protected_existing_files_unchanged_during_check"] = len(before)
    result["Spec_sha256"] = SPEC_SHA256
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
