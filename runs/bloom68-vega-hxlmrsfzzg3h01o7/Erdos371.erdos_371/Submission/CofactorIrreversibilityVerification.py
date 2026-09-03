#!/usr/bin/env python3
"""Finite checks for CofactorIrreversibilityResearch.md.

Only ordinary integer arithmetic is used.  No Lean file is imported or used.
The Hildebrand stable-set theorem and the asymptotic prime estimates quoted in
that note are mathematical inputs, not conclusions of this finite test.
"""
from collections import Counter, defaultdict, deque
from math import gcd, isqrt


def largest_primes(limit):
    p = [1] * (limit + 1)
    for q in range(2, limit + 1):
        if p[q] == 1:
            p[q::q] = [q] * (limit // q)
    return p


def order(a, b):
    return (b > a) - (b < a)


def arithmetic_checks(p, q):
    limit = len(p) - 1
    for n in range(3, limit):
        a, b = q[n], q[n + 1]
        assert a != b and gcd(a, b) == 1
        assert order(p[n], p[n + 1]) == -order(a, b)
        assert n == a * p[n] and n + 1 == b * p[n + 1]
        assert p[a] <= p[n] and p[b] <= p[n + 1]
        if min(p[n], p[n + 1]) > 2:
            assert (a - b) % 2 == 1
    checks = 0
    for a in range(1, 4001):
        for b in range(1, 4001 // a + 1):
            assert p[a * b] == max(p[a], p[b])
            checks += 1
    for h in (1, 2, 3, 10, 100, 1000, 10000, 100001):
        multiplicities = Counter(q[1:h + 1])
        actual = set(multiplicities)
        predicted = {a for a in range(1, h + 1) if a * p[a] <= h}
        assert actual == predicted
        for a in actual:
            if a > 1:
                expected = sum(p[r] == r for r in range(p[a], h // a + 1))
                assert multiplicities[a] == expected
    print(f"Arithmetic: {limit - 3:,} edge checks; {checks:,} max-product checks; "
          "8 exact vertex/multiplicity checks.")


def potential_obstruction_checks(p, q):
    """Exact dyadic mixed-cycle certificates for arbitrary prime potentials
    and for completely additive cofactor potentials (integer sample weights).
    """
    x = 100000
    h = [((r * r * 19 + 7) % 131) - 65 for r in range(x + 2)]
    weight = [((r * 37 + 11) % 101) - 50 for r in range(x + 2)]
    f = [0] * (x + 2)
    for m in range(2, x + 2):
        f[m] = f[m // p[m]] + weight[p[m]]
    for a in range(1, (x + 1) // 2 + 1):
        assert f[2 * a] == f[a] + weight[2]
    s = [0] * (x + 1)
    gp = [0] * (x + 1)
    gq = [0] * (x + 1)
    for n in range(3, x + 1):
        s[n] = order(p[n], p[n + 1])
        gp[n] = h[p[n + 1]] - h[p[n]]
        gq[n] = f[q[n + 1]] - f[q[n]]
    m = (x - 1) // 2
    for n in range(3, m + 1):
        assert p[2 * n] == p[n] and p[2 * n + 2] == p[n + 1]
        assert len({p[n], p[n + 1], p[2 * n + 1]}) == 3
        assert abs(s[2 * n] + s[2 * n + 1] - s[n]) == 1
        assert gp[2 * n] + gp[2 * n + 1] - gp[n] == 0
        assert gq[2 * n] + gq[2 * n + 1] - gq[n] == 0
    removals = [set(), {n for n in range(3, x + 1) if n % 17 == 0},
                {n for n in range(3, x + 1) if max(p[n], p[n + 1]) > x // 2}]
    for deleted in removals:
        remaining_triangles = [n for n in range(3, m + 1)
                               if not ({n, 2 * n, 2 * n + 1} & deleted)]
        incidence = Counter(t for n in remaining_triangles for t in (n, 2 * n, 2 * n + 1))
        assert max(incidence.values(), default=0) <= 2
        assert len(remaining_triangles) >= m - 2 - 2 * len(deleted)
        for errors in ([s[n] - gp[n] for n in range(x + 1)],
                       [s[n] + gq[n] for n in range(x + 1)]):
            total_error = sum(abs(errors[n]) for n in range(3, x + 1) if n not in deleted)
            triangle_error = sum(abs(errors[n]) * v for n, v in incidence.items())
            assert 2 * total_error >= triangle_error >= len(remaining_triangles)
            assert 2 * total_error >= max(0, m - 2 - 2 * len(deleted))
    print(f"Potential obstruction: {m - 2:,} exact dyadic defects of absolute value 1; "
          "two potential classes and three deletion sets checked.")



def graph_statistics(x, labels, start):
    c = Counter((labels[n], labels[n + 1]) for n in range(start, x + 1))
    vertices = set(labels[start:x + 2])
    loops = sum(v for (a, b), v in c.items() if a == b)
    assert loops == 0
    l1 = sum(abs(c[a, b] - c[b, a]) for a, b in c if a < b)
    # The previous expression omits unordered pairs appearing only downward.
    l1 += sum(c[a, b] for a, b in c if a > b and (b, a) not in c)
    # Independent normalization check, avoiding any missing-key ambiguity.
    unordered = {tuple(sorted((a, b))) for a, b in c}
    assert l1 == sum(abs(c[a, b] - c[b, a]) for a, b in unordered)
    cancelled_pairs = sum(min(c[a, b], c[b, a]) for a, b in unordered)
    assert l1 == x - start + 1 - 2 * cancelled_pairs
    forced = []
    residues = {}
    for n in range(start, x + 1):
        a, b = labels[n], labels[n + 1]
        ab = a * b
        if (a, b) in residues:
            assert (n - residues[a, b]) % ab == 0
        else:
            residues[a, b] = n
        if (b, a) in residues:
            assert (n + residues[b, a] + 1) % ab == 0
        if ab > 2 * x + 1:
            assert c[a, b] == 1 and c[b, a] == 0
            forced.append(n)
    assert len({tuple(sorted((labels[n], labels[n + 1]))) for n in forced}) == len(forced)
    assert l1 >= len(forced)
    return len(vertices), l1, forced


def deletion_checks(x, p, q, forced):
    prime_sets = [
        {2},
        {r for r in range(2, 21) if p[r] == r},
        {r for r in range(2, x + 2) if p[r] == r and r ** 4 >= x and r ** 3 <= x},
        {r for r in range(2, x + 2) if p[r] == r and 2 * r > x},
    ]
    forced_set = set(forced)
    for primes in prime_sets:
        removed = {n for n in range(3, x + 1) if p[n] in primes or p[n + 1] in primes}
        cover_bound = 2 * sum((x + 1) // r for r in primes)
        assert len(removed) <= cover_bound
        c = Counter((q[n], q[n + 1]) for n in range(3, x + 1) if n not in removed)
        unordered = {tuple(sorted((a, b))) for a, b in c}
        l1 = sum(abs(c[a, b] - c[b, a]) for a, b in unordered)
        assert l1 >= len(forced_set - removed) >= len(forced) - len(removed)
    print(f"  X={x}: four prime-class deletion/cover inequalities verified.")


def cancel_and_decompose(x, p, q):
    """Use each real edge at most once; returned cycles have no artificial edge."""
    groups = defaultdict(list)
    deleted_two = []
    for n in range(3, x + 1):
        if min(p[n], p[n + 1]) == 2:
            deleted_two.append(n)
        else:
            groups[q[n], q[n + 1]].append(n)
    unordered = {tuple(sorted(key)) for key in groups}
    adjacency = defaultdict(list)
    retained = set()
    cancelled = 0
    for a, b in sorted(unordered):
        ab, ba = groups.get((a, b), []), groups.get((b, a), [])
        k = min(len(ab), len(ba))
        cancelled += 2 * k
        for n in ab[k:] + ba[k:]:
            adjacency[q[n]].append(n)
            retained.add(n)
    assert len(retained) + cancelled + len(deleted_two) == x - 2
    div = Counter()
    for n in retained:
        div[q[n]] += 1
        div[q[n + 1]] -= 1
        assert (q[n] - q[n + 1]) % 2
    boundary = sum(max(0, v) for v in div.values())
    assert boundary <= len(deleted_two) + 1
    v_count = len(set(q[3:x + 2]))
    live = {a for a in adjacency if adjacency[a]}
    seen = set()
    cycle_edges = path_edges = cycle_forced = path_forced = 0
    cycles = paths = max_length = 0
    cycle_current = path_current = 0
    certificate = None

    def forced(n):
        return q[n] * q[n + 1] > 2 * x + 1

    while live:
        source = next((a for a in live if div[a] > 0), None)
        if source is None:
            source = min(live)
        vertex_word = [source]
        position = {source: 0}
        edge_word = []
        a = source
        while adjacency[a]:
            n = adjacency[a].pop()
            if not adjacency[a]:
                live.discard(a)
            assert n not in seen
            seen.add(n)
            b = q[n + 1]
            assert q[n] == a
            div[a] -= 1
            div[b] += 1
            if b not in position:
                edge_word.append(n)
                position[b] = len(vertex_word)
                vertex_word.append(b)
            else:
                k = position[b]
                edges = edge_word[k:] + [n]
                labels = [q[m] for m in edges]
                assert len(labels) == len(set(labels))
                assert all(q[edges[i] + 1] == q[edges[(i + 1) % len(edges)]]
                           for i in range(len(edges)))
                assert len(edges) >= 4 and len(edges) % 2 == 0
                assert all(m in retained for m in edges)
                cycles += 1
                cycle_edges += len(edges)
                cycle_forced += sum(forced(m) for m in edges)
                w = sum(order(q[m], q[m + 1]) for m in edges)
                assert w % 2 == 0
                cycle_current += w
                if w and (certificate is None or len(edges) < len(certificate[0])):
                    certificate = (edges, labels, w)
                max_length = max(max_length, len(edges))
                for old in vertex_word[k + 1:]:
                    del position[old]
                vertex_word = vertex_word[:k + 1]
                edge_word = edge_word[:k]
            a = b
        if edge_word:
            assert len(edge_word) <= v_count - 1
            assert len(vertex_word) == len(set(vertex_word))
            paths += 1
            path_edges += len(edge_word)
            path_forced += sum(forced(n) for n in edge_word)
            path_current += sum(order(q[n], q[n + 1]) for n in edge_word)
    assert seen == retained
    assert all(v == 0 for v in div.values())
    assert paths == boundary
    assert path_edges <= boundary * (v_count - 1)
    assert cycle_edges + path_edges == len(retained)
    retained_forced = sum(forced(n) for n in retained)
    assert cycle_forced + path_forced == retained_forced
    assert cycle_forced >= retained_forced - boundary * (v_count - 1)
    assert cycle_current + path_current == sum(order(q[n], q[n + 1]) for n in retained)
    print(f"  X={x}: deleted LPF-2 edges={len(deleted_two)}, cancelled={cancelled}, "
          f"retained={len(retained)}, cycles={cycles}, cycle edges={cycle_edges}, "
          f"paths={paths}, path edges={path_edges}, max cycle={max_length}, "
          f"irreversible cycle edges={cycle_forced}.")
    return certificate


def k_core_check(x, q, forced, k):
    """Undirected total-degree pruning only; no in/out-degree claim is made."""
    adjacency = defaultdict(set)
    for n in forced:
        adjacency[q[n]].add(n)
        adjacency[q[n + 1]].add(n)
    initial_vertices = len(adjacency)
    remaining = set(forced)
    queue = deque(a for a in adjacency if len(adjacency[a]) < k)
    pruned = set()
    while queue:
        a = queue.popleft()
        if a in pruned:
            continue
        assert len(adjacency[a]) < k
        pruned.add(a)
        for n in list(adjacency[a]):
            if n not in remaining:
                continue
            remaining.remove(n)
            b = q[n + 1] if q[n] == a else q[n]
            adjacency[b].remove(n)
            if len(adjacency[b]) < k:
                queue.append(b)
        adjacency[a].clear()
    lost = len(forced) - len(remaining)
    assert lost <= (k - 1) * initial_vertices
    assert all(len(edges) >= k for a, edges in adjacency.items() if a not in pruned)
    print(f"  X={x}: {k}-core of irreversible graph: "
          f"{len(remaining)} / {len(forced)} edges retained; pruning bound verified.")


def main():
    limit = 1_000_001
    p = largest_primes(limit)
    q = [0] + [n // p[n] for n in range(1, limit + 1)]
    arithmetic_checks(p, q)
    potential_obstruction_checks(p, q)
    print("X | V(cofactor) | L1(cofactor) | irreversible(cofactor) | signed I | "
          "L1(prime) | both prime labels > sqrt(2X+1)")
    samples = {}
    for x in (1000, 10000, 100000, 1000000):
        v, l1, forced = graph_statistics(x, q, 3)
        pv, pl1, pf = graph_statistics(x, p, 2)
        high = [n for n in range(2, x + 1)
                if min(p[n], p[n + 1]) ** 2 > 2 * x + 1]
        assert set(high) <= set(pf)
        assert pl1 >= len(high)
        cofactor_current = sum(order(q[n], q[n + 1]) for n in range(3, x + 1))
        s = sum(order(p[n], p[n + 1]) for n in range(1, x + 1))
        assert s == 2 - cofactor_current
        signed_i = sum(order(p[n], p[n + 1]) for n in forced)
        print(f"{x} | {v} | {l1} | {len(forced)} | {signed_i} | {pl1} | {len(high)}")
        samples[x] = forced
    irreversible_cycle = [186353, 456246, 842897, 925806]
    assert set(irreversible_cycle) <= set(samples[1000000])
    assert [q[n] for n in irreversible_cycle] == [331, 6426, 7733, 13818]
    assert all(q[irreversible_cycle[i] + 1] == q[irreversible_cycle[(i + 1) % 4]]
               for i in range(4))
    assert sum(order(q[n], q[n + 1]) for n in irreversible_cycle) == 2
    assert all(min(p[n], p[n + 1]) > 2 for n in irreversible_cycle)
    print("Fully irreversible biased four-cycle at X=1,000,000 verified:", irreversible_cycle)
    print("Prime deletion checks:")
    for x in (1000, 10000, 100000):
        deletion_checks(x, p, q, samples[x])
    print("Actual edge-disjoint cycle decompositions after all opposite-edge cancellations:")
    certificate = None
    for x in (1000, 10000, 100000):
        certificate = cancel_and_decompose(x, p, q)
    if certificate:
        edges, labels, w = certificate
        print("One retained biased cycle (illustration, not the asymptotic obstruction):")
        print("  indices=", edges)
        print("  cofactor vertices=", labels, "; cofactor current=", w)
        print("  prime-label pairs=", [(p[n], p[n + 1]) for n in edges])
    print("Degree pruning:")
    for x, k in ((1000, 2), (10000, 3), (100000, 4), (1000000, 5)):
        k_core_check(x, q, samples[x], k)
    print("PASS. These finite checks do not prove Hildebrand's theorem, "
          "a density asymptotic, or cancellation of S(X).")


if __name__ == "__main__":
    main()
