#!/usr/bin/env python3
"""Deterministic audits of the homomorphism-capacity derivations.

This is not a search for Ramsey counterexamples.  It checks specified
constructions, exact rational matching certificates, and counting identities.
No project Lean file or unproved specification theorem is imported.
"""
from collections import Counter, deque
from fractions import Fraction as F
from itertools import product
from math import cos, pi, sqrt


def edge(u, v):
    return (u, v) if u <= v else (v, u)


def binomial_counts(d):
    out = [1]
    for j in range(d):
        out.append(out[-1] * (d - j) // (j + 1))
    assert sum(out) == 1 << d
    return out


def matching_certificate(q, edges, primal, dual):
    """Exact primal/dual certificates, loops having incidence two."""
    loads = [F(0) for _ in range(q)]
    for (u, v), x in primal.items():
        assert (u, v) in edges and x >= 0
        loads[u] += x
        loads[v] += x
    assert all(x <= 1 for x in loads)
    assert len(dual) == q and all(z >= 0 for z in dual)
    assert all(dual[u] + dual[v] >= 1 for u, v in edges)
    nu = sum(primal.values(), F(0))
    assert nu == sum(dual, F(0)) > 0
    p = [load / (2 * nu) for load in loads]
    atoms = [(u, v, x / nu) for (u, v), x in primal.items() if x]
    assert sum(p, F(0)) == 1 and max(p) == 1 / (2 * nu)
    return nu, p, atoms


def shortest_path(q, edges, start, finish):
    queue = deque([start])
    pred = {start: None}
    while queue:
        u = queue.popleft()
        if u == finish:
            path = []
            while u is not None:
                path.append(u)
                u = pred[u]
            return list(reversed(path))
        for v in range(q):
            if v not in pred and edge(u, v) in edges:
                pred[v] = u
                queue.append(v)
    raise ValueError("The chosen atoms are in different components")


def phase_walk(q, edges, atoms, d):
    """Quantile blocks, joined by actual paths, not independent phases."""
    counts = binomial_counts(d)
    h = 1 << d
    cumulative = []
    total = 0
    for count in counts:
        total += count
        cumulative.append(total)
    cuts = [-1]
    target = F(0)
    for _, _, mass in atoms[:-1]:
        target += mass
        cuts.append(next(j for j, value in enumerate(cumulative)
                         if value * target.denominator >= h * target.numerator))
    cuts.append(d)
    blocks = [(cuts[i] + 1, cuts[i + 1]) for i in range(len(atoms))]
    assert all(b - a + 1 >= q for a, b in blocks)
    walk = []
    for i, ((u, v, _), (a, b)) in enumerate(zip(atoms, blocks)):
        assert len(walk) == a
        if i == 0:
            walk.append(u)
        else:
            route = shortest_path(q, edges, walk[-1], u)
            walk.extend(route[1:])
        while len(walk) <= b:
            walk.append(v if walk[-1] == u else u)
    assert len(walk) == d + 1
    assert all(edge(walk[j], walk[j + 1]) in edges for j in range(d))
    return walk, counts


def audit_weight_walk(q, edges, walk, counts, target):
    d = len(walk) - 1
    h = 1 << d
    occupancies = [0] * q
    for v, count in zip(walk, counts):
        occupancies[v] += count
    edge_counts = Counter()
    for j in range(d):
        e = edge(walk[j], walk[j + 1])
        assert e in edges
        edge_counts[e] += counts[j] * (d - j)
    assert sum(edge_counts.values()) == d * h // 2
    incidences = [0] * q
    for (u, v), count in edge_counts.items():
        incidences[u] += count
        incidences[v] += count  # twice at the same vertex for a loop
    assert incidences == [d * n for n in occupancies]
    p = [F(n, h) for n in occupancies]
    # The flow produced by ANY homomorphism is a fractional matching after
    # dividing its edge probabilities by 2*max(p).
    b = max(p)
    flow_loads = [F(0)] * q
    flow_total = F(0)
    for (u, v), count in edge_counts.items():
        x = F(count, d * h) / b
        flow_loads[u] += x
        flow_loads[v] += x
        flow_total += x
    assert max(flow_loads) <= 1 and flow_total == 1 / (2 * b)
    return p, max(abs(x - y) for x, y in zip(p, target))


def check_fractional_limits():
    examples = []
    examples.append(("P4", 4, {(0, 1), (1, 2), (2, 3)},
                     {(0, 1): F(1), (2, 3): F(1)},
                     [F(0), F(1), F(1), F(0)]))
    examples.append(("C5", 5, {edge(i, (i + 1) % 5) for i in range(5)},
                     {edge(i, (i + 1) % 5): F(1, 2) for i in range(5)},
                     [F(1, 2)] * 5))
    examples.append(("star_4", 5, {(0, i) for i in range(1, 5)},
                     {(0, i): F(1, 4) for i in range(1, 5)},
                     [F(1)] + [F(0)] * 4))
    examples.append(("path_with_loop", 3, {(0, 1), (1, 2), (2, 2)},
                     {(0, 1): F(1), (2, 2): F(1, 2)},
                     [F(1, 2)] * 3))
    examples.append(("K_2_5", 7, {(u, v) for u in range(2) for v in range(2, 7)},
                     {(u, v): F(1, 5) for u in range(2) for v in range(2, 7)},
                     [F(1), F(1)] + [F(0)] * 5))
    for name, q, edges, primal, dual in examples:
        nu, target, atoms = matching_certificate(q, edges, primal, dual)
        for d in [4096, 8192]:
            walk, counts = phase_walk(q, edges, atoms, d)
            p, error = audit_weight_walk(q, edges, walk, counts, target)
            r = len(atoms)
            coefficient = 3 * r + (r - 1) * (q - 1)
            assert error <= coefficient * F(max(counts), 1 << d)
            assert max(p) >= 1 / (2 * nu)
            print(f"phase {name:15s} d={d:4d}: alpha={float(1/(2*nu)):.6f}, "
                  f"max fibre/h={float(max(p)):.6f}, error={float(error):.6f}")
    # A matching in two DIFFERENT components must not be aggregated.
    try:
        shortest_path(4, {(0, 1), (2, 3)}, 0, 2)
    except ValueError:
        pass
    else:
        raise AssertionError("Disconnected matching support was joined")
    print("Exact matching primal/dual, loop incidence, component, and edge-flow audits passed.")


def residue_counts(t, ell):
    out = [0] * ell
    for j, count in enumerate(binomial_counts(t)):
        out[j % ell] += count
    return out


def check_residue_bounds():
    checked = 0
    for ell in range(3, 25):
        for t in [1, 2, 3, 8, 17, 64, 127, 256, 1024]:
            counts = residue_counts(t, ell)
            actual = max(counts) / (1 << t)
            rho = cos(pi / ell)
            fourier_bound = (1 + (ell - 1) * rho**t) / ell
            gaussian_bound = 1 / ell + sqrt(2 / pi) / sqrt(t)
            assert actual <= fourier_bound + 2e-14
            assert actual <= gaussian_bound + 2e-14
            if t >= ell * ell:
                assert actual < 2 / ell
            checked += 1
    print(f"Binomial residues: {checked} prescribed (t,ell) pairs; both parities of ell included.")


def torus_adj(u, v, ell):
    differences = [(a - b) % ell for a, b in zip(u, v)]
    nonzero = [a for a in differences if a]
    return len(nonzero) == 1 and nonzero[0] in (1, ell - 1)


def check_ordinary_torus_lift():
    # A specified strict homomorphism Q_16 -> C5 square C5, then a genuine
    # injection into its s-blow-up.  Interiors are explicitly two-coloured.
    d, k, ell, block = 16, 2, 5, 8
    vertices = list(product(range(ell), repeat=k))
    index = {v: i for i, v in enumerate(vertices)}
    residue = residue_counts(block, ell)
    s = max(residue) ** k
    used = [0] * len(vertices)
    injection = []
    labels = []
    for x in range(1 << d):
        t = (((x & 255).bit_count()) % ell, ((x >> 8).bit_count()) % ell)
        i = index[t]
        labels.append(t)
        injection.append(i * s + used[i])
        used[i] += 1
    assert max(used) == s
    assert len(set(injection)) == 1 << d

    def colour(a, b):
        i, r = divmod(a, s)
        j, t = divmod(b, s)
        assert a != b
        if i == j:
            return (r + t) % 2  # red and blue, not a forbidden third colour
        return 0 if torus_adj(vertices[i], vertices[j], ell) else 1

    edges_checked = 0
    for x, a in enumerate(injection):
        for j in range(d):
            y = x ^ (1 << j)
            if x < y:
                assert labels[x] != labels[y]
                assert colour(a, injection[y]) == 0
                edges_checked += 1
    assert edges_checked == d * (1 << (d - 1))
    assert colour(0, 1) == 1 and colour(0, 2) == 0
    print(f"Ordinary torus lift: {1<<d} distinct vertices, {edges_checked} red cube edges, "
          f"25 clusters of capacity {s}; arbitrary two-coloured interiors audited.")


def check_nonlinear_lattice_lift():
    # Distance to a non-singleton set is generally nonlinear and 1-Lipschitz.
    # This tests stationary (within-cluster) steps as well as nonzero ones.
    d, k, ell, block = 8, 2, 5, 4
    anchors = [0, 0b1011, 0b1100]
    height = [min((x ^ a).bit_count() for a in anchors) for x in range(1 << block)]
    image = [(height[x & 15] % ell, height[x >> 4] % ell) for x in range(1 << d)]
    lifted = {0: (0, 0)}
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for j in range(d):
            y = x ^ (1 << j)
            delta = tuple((image[y][i] - image[x][i]) % ell for i in range(k))
            assert sum(a != 0 for a in delta) <= 1
            assert all(a in (0, 1, ell - 1) for a in delta)
            step = tuple(-1 if a == ell - 1 else a for a in delta)
            candidate = tuple(a + b for a, b in zip(lifted[x], step))
            if y in lifted:
                assert lifted[y] == candidate
            else:
                lifted[y] = candidate
                queue.append(y)
    h = 1 << d
    mean = [F(sum(lifted[x][j] for x in lifted), h) for j in range(k)]
    variance = sum(sum((F(lifted[x][j]) - mean[j])**2 for j in range(k))
                   for x in lifted) / h
    energy = F(0)
    for x in range(h):
        for j in range(d):
            y = x ^ (1 << j)
            energy += sum((lifted[x][a] - lifted[y][a])**2 for a in range(k))
    energy /= 4 * h
    assert variance <= energy <= F(d, 4)
    max_fibre = max(Counter(image).values()) / h
    lower = 1 / (2 * (3 * (1 + sqrt(d / k)))**k)
    assert max_fibre >= max(ell**(-k), lower)
    # Balanced extension by folding an extra cube coordinate into the first.
    extended = []
    for x in range(1 << (d + 1)):
        folded = (x & (h - 1)) ^ ((x >> d) & 1)
        extended.append(image[folded])
    assert Counter(extended) == Counter({v: 2 * n for v, n in Counter(image).items()})
    for x in range(1 << (d + 1)):
        for j in range(d + 1):
            a, b = extended[x], extended[x ^ (1 << j)]
            assert a == b or torus_adj(a, b, ell)
    print(f"Nonlinear lazy lattice lift: path-independent, variance={variance}, "
          f"energy={energy} <= d/4; exact balanced coordinate fold audited.")


def check_complementary_torus_pools():
    for ell in range(5, 101):
        a = (ell - 2) // 2
        A = range(a)
        B = range(a + 1, 2 * a + 1)
        assert 5 * a >= ell
        for u in A:
            for v in B:
                assert (u - v) % ell not in (0, 1, ell - 1)
        for k in range(1, 6):
            m = ell**k
            pool = a * ell**(k - 1)
            assert 5 * pool >= m
    print("Complementary torus colour: explicit complete bipartite pools >= m/5 each, "
          "all tested ell=5..100 and k=1..5.")


def check_three_cluster_threshold():
    for d in range(2, 13):
        h = 1 << d
        s = h // 2 - 1
        # Red components are cliques of sizes 2s and s.  Blue is K_(2s,s).
        assert 2 * s < h and s < h // 2
        assert 3 * s == 3 * h // 2 - 3
        # At capacity h/2 there is an actual red injection into clusters 0,1.
        capacity = h // 2
        images = [(x & 1) * capacity + (x >> 1) for x in range(h)]
        assert len(set(images)) == h
        for x in range(h):
            for j in range(d):
                a, b = images[x], images[x ^ (1 << j)]
                ia, ib = a // capacity, b // capacity
                assert a != b and (ia == ib or {ia, ib} == {0, 1})
    print("Three-cluster exact threshold: kappa_d=2^(d-1), d=2..12; "
          "constant 3/2 lower construction only, not an unbounded ratio.")


def check_local_density_certificate():
    checked = 0
    for m in range(2, 43):
        colourings = [
            {(u, v) for u in range(m) for v in range(u + 1, m) if (u < m // 2) == (v < m // 2)},
            {(u, v) for u in range(m) for v in range(u + 1, m) if u + v < m},
            {(u, v) for u in range(m) for v in range(u + 1, m) if (u - v) % 5 in (1, 4)},
        ]
        complete = {(u, v) for u in range(m) for v in range(u + 1, m)}
        for red in colourings:
            for edges in [red, complete - red]:
                if not edges:
                    continue
                neighbours = [set() for _ in range(m)]
                for u, v in edges:
                    neighbours[u].add(v)
                    neighbours[v].add(u)
                degrees = list(map(len, neighbours))
                sums = [sum(degrees[u] for u in neighbours[v]) for v in range(m)]
                assert sum(sums) == sum(a * a for a in degrees)
                v = max(range(m), key=lambda j: sums[j])
                local_edges = {e for e in edges if e[0] in neighbours[v] or e[1] in neighbours[v]}
                assert 2 * len(local_edges) >= sums[v]
                assert len(local_edges) * m * m >= 2 * len(edges)**2
                if 2 * len(edges) >= len(complete):
                    assert F(len(local_edges), m) >= F((m - 1)**2, 8 * m)
                checked += 1
    print(f"Triangle-square-cover local density certificate: {checked} prescribed colour graphs; "
          "exact incidence counts and the majority-colour lower bound passed.")


if __name__ == "__main__":
    check_fractional_limits()
    check_residue_bounds()
    check_ordinary_torus_lift()
    check_nonlinear_lattice_lift()
    check_complementary_torus_pools()
    check_three_cluster_threshold()
    check_local_density_certificate()
    print("PASS: all deterministic audits. No Ramsey disproof is claimed.")
