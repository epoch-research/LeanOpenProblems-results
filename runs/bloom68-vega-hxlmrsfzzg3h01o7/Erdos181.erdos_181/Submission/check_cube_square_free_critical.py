#!/usr/bin/env python3
"""Independent finite/algebraic audits for CubeSquareFreeCriticalEstimate.md.

These checks do NOT assert the open cube-free critical comparison or the
Ramsey bound for Q_d.  All square graphs below are rebuilt from their actual
remaining original edges, including both diagonals of every rectangle.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod
from random import Random
import hashlib
from pathlib import Path


SPEC_SHA256 = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def full_square(a, b, edges):
    adj = {f: set() for f in edges}
    rectangles = 0
    for x, xx in combinations(range(a), 2):
        for y, yy in combinations(range(b), 2):
            cells = ((x, y), (x, yy), (xx, y), (xx, yy))
            if all(f in edges for f in cells):
                rectangles += 1
                for f, g in ((cells[0], cells[3]), (cells[1], cells[2])):
                    adj[f].add(g)
                    adj[g].add(f)
    assert sum(map(len, adj.values())) == 4 * rectangles
    return adj, 2 * rectangles


def moments(a, b, edges):
    rows = [{y for x0, y in edges if x0 == x} for x in range(a)]
    cols = [{x for x, y0 in edges if y0 == y} for y in range(b)]
    da = sum(len(r) ** 2 for r in rows)
    db = sum(len(c) ** 2 for c in cols)
    t4 = sum(len(x & y) ** 2 for x in rows for y in rows)
    return rows, cols, da, db, t4


def matching_number(edges):
    rows = {}
    for x, y in edges:
        rows.setdefault(x, []).append(y)
    match = {}

    def augment(x, seen):
        for y in rows.get(x, []):
            if y in seen:
                continue
            seen.add(y)
            if y not in match or augment(match[y], seen):
                match[y] = x
                return True
        return False

    return sum(augment(x, set()) for x in rows)


def peel(a, b, edges, threshold):
    current = set(edges)
    _, initial = full_square(a, b, current)
    steps = 0
    while current:
        adj, before = full_square(a, b, current)
        low = [f for f in current if len(adj[f]) <= threshold]
        if not low:
            break
        f = min(low)
        degree = len(adj[f])
        current.remove(f)
        _, after = full_square(a, b, current)
        # Removing an ORIGINAL edge destroys both diagonals of its rectangles.
        assert before - after == 2 * degree
        steps += 1
    adj, final = full_square(a, b, current)
    assert initial - final <= 2 * threshold * len(edges)
    assert initial - final <= 2 * threshold * steps
    assert all(len(adj[f]) > threshold for f in current)
    return current, adj, final


def lift_prism(labels, parent):
    """Return a bipartition-respecting map of T x K_2, using parity twisting."""
    m = len(parent)
    parity = [0] * m
    for i in range(1, m):
        parity[i] = 1 - parity[parent[i]]
    result = {}
    for i, (x, y) in enumerate(labels):
        for t in (0, 1):
            result[i, t] = ("A", x) if t == parity[i] else ("B", y)
    return result


def audit_prism(a, b, edges, labels, parent):
    image = lift_prism(labels, parent)
    m = len(parent)
    assert len(set(image.values())) == 2 * m

    def is_edge(u, v):
        x, y = image[u], image[v]
        if x[0] == "B":
            x, y = y, x
        return x[0] == "A" and y[0] == "B" and (x[1], y[1]) in edges

    assert all(is_edge((i, 0), (i, 1)) for i in range(m))
    assert all(is_edge((i, t), (parent[i], t))
               for i in range(1, m) for t in (0, 1))


def greedy_prism(a, b, edges, adj, parent):
    m = len(parent)
    assert edges
    assert min(map(len, adj.values())) > (m - 2) * (a + b - 1)
    labels = [min(edges)]
    for i in range(1, m):
        used_a = {x for x, _ in labels}
        used_b = {y for _, y in labels}
        choices = [f for f in adj[labels[parent[i]]]
                   if f[0] not in used_a and f[1] not in used_b]
        assert choices
        labels.append(min(choices))
    audit_prism(a, b, edges, labels, parent)
    return labels


def cut_discrepancy_numerators(a, b, edges):
    ab = a * b
    e = len(edges)
    pos = 0
    absolute = 0
    for xs in range(1, 1 << a):
        xx = [x for x in range(a) if xs >> x & 1]
        for ys in range(1, 1 << b):
            yy = [y for y in range(b) if ys >> y & 1]
            count = sum((x, y) in edges for x in xx for y in yy)
            value = ab * count - e * len(xx) * len(yy)
            pos = max(pos, value)
            absolute = max(absolute, abs(value))
    # Both are numerators over (ab)^2 for normalized discrepancy.
    return pos, absolute


def audit_energy(a, b, edges, cached=None):
    ab = a * b
    e = len(edges)
    rows, cols, da, db, t4 = moments(a, b, edges)
    delta_num = t4 * ab * ab - e ** 4
    assert delta_num >= 0
    pos, absolute = cached or cut_discrepancy_numerators(a, b, edges)
    assert delta_num <= 4 * absolute * ab * ab
    assert delta_num <= 12 * pos * ab * ab

    p = F(e, ab)
    tau = F(t4, ab * ab)
    eta = tau - p ** 4
    for q in (F(da, a * b * b), F(db, b * a * a)):
        var = q - p * p
        assert var >= 0
        assert 2 * p * p * var <= eta
        mse = tau - 2 * p * p * q + p ** 4
        assert 0 <= mse <= eta

    # Independently calculate the fourth Schatten moment of M-pJ.
    w = [[ab * int((x, y) in edges) - e for y in range(b)]
         for x in range(a)]
    gram = [[sum(w[x][y] * w[xx][y] for y in range(b))
             for xx in range(a)] for x in range(a)]
    schatten_num = sum(z * z for row in gram for z in row)
    assert schatten_num <= 6 * delta_num * ab * ab
    return pos, absolute


def injective_count(a, b, edges, left_size, right_size, source_edges):
    count = 0
    for aa in permutations(range(a), left_size):
        for bb in permutations(range(b), right_size):
            count += all((aa[x], bb[y]) in edges for x, y in source_edges)
    return count


def falling(n, r):
    return prod(range(n - r + 1, n + 1))


def audit_injective_cut(a, b, edges, l, r, source_edges, absolute):
    count = injective_count(a, b, edges, l, r, source_edges)
    normalized = F(count, falling(a, l) * falling(b, r))
    p = F(len(edges), a * b)
    kappa = F(absolute, (a * b) ** 2)
    prefactor = F(a * b, (a - l + 1) * (b - r + 1))
    assert abs(normalized - p ** len(source_edges)) <= len(source_edges) * prefactor * kappa


def cube_bipartite(d):
    aa = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
    bb = [x for x in range(1 << d) if x.bit_count() % 2 == 1]
    ix, iy = {x: i for i, x in enumerate(aa)}, {y: i for i, y in enumerate(bb)}
    return [(ix[x], iy[x ^ (1 << j)]) for x in aa for j in range(d)]


def exhaustive_small():
    total = deletions = prism_tests = 0
    for a, b in ((1, 1), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4)):
        cells = list(product(range(a), range(b)))
        for mask in range(1 << (a * b)):
            edges = {f for i, f in enumerate(cells) if mask >> i & 1}
            adj, s = full_square(a, b, edges)
            _, _, da, db, t4 = moments(a, b, edges)
            assert t4 == 2 * s + da + db - len(edges)
            for f in edges:
                _, ss = full_square(a, b, edges - {f})
                assert s - ss == 2 * len(adj[f])
                deletions += 1
                nu = matching_number(adj[f])
                assert len(adj[f]) <= nu * max(0, a + b - 2)
            thresholds = {F(0), F(1), F(2), F(3)}
            if edges:
                thresholds.add(F(s, 4 * len(edges)))
            for threshold in thresholds:
                core, cadj, ss = peel(a, b, edges, threshold)
                if edges and threshold == F(s, 4 * len(edges)):
                    assert ss >= F(s, 2)
                if core:
                    for m in (2, 3):
                        if min(map(len, cadj.values())) > (m - 2) * (a + b - 1):
                            greedy_prism(a, b, core, cadj, [-1] + list(range(m - 1)))
                            prism_tests += 1
            pos, absolute = audit_energy(a, b, edges)
            complement = set(cells) - edges
            _, blue_s = full_square(a, b, complement)
            _, _, bda, bdb, blue_t4 = moments(a, b, complement)
            assert 8 * (t4 + blue_t4) >= (a * b) ** 2
            assert da + db + bda + bdb - a * b <= (a + b - 1) * a * b
            assert 16 * (s + blue_s) >= (a * b) ** 2 - 8 * (a + b - 1) * a * b
            if a >= 2 and b >= 2:
                audit_injective_cut(a, b, edges, 2, 2, list(product(range(2), repeat=2)), absolute)
            total += 1
    return total, deletions, prism_tests


def extra_tests():
    rng = Random(181)
    cube = cube_bipartite(3)
    for _ in range(256):
        edges = {(x, y) for x in range(4) for y in range(4) if rng.randrange(2)}
        _, absolute = audit_energy(4, 4, edges)
        audit_injective_cut(4, 4, edges, 4, 4, cube, absolute)
        for threshold in (F(0), F(2), F(5), F(7)):
            core, cadj, _ = peel(4, 4, edges, threshold)
            if core and min(map(len, cadj.values())) > 7:
                greedy_prism(4, 4, core, cadj, [-1, 0, 1])
    # Entire source-label set is injected; all prism edges are checked.
    for m in (2, 3, 4, 5, 8, 16):
        t = 2 * m - 2
        edges = set(product(range(t), repeat=2))
        adj, _ = full_square(t, t, edges)
        for parent in ([-1] + [0] * (m - 1), [-1] + list(range(m - 1)),
                       [-1] + [(i - 1) // 2 for i in range(1, m)]):
            greedy_prism(t, t, edges, adj, parent)


def switching_tests():
    # Index a matching as the diagonal, and enumerate ACTUAL host matrices.
    t = 4
    other = [(x, y) for x in range(t) for y in range(t) if x != y]
    switches = 0
    for mask in range(1 << len(other)):
        edges = {(i, i) for i in range(t)} | {f for j, f in enumerate(other) if mask >> j & 1}
        b = [[int((i, j) in edges) for j in range(t)] for i in range(t)]
        old = sum(b[i][j] * b[j][i] for i in range(t) for j in range(i + 1, t))
        for i, j in combinations(range(t), 2):
            if not (b[i][j] and b[j][i]):
                continue
            pi = list(range(t))
            pi[i], pi[j] = pi[j], pi[i]
            labels = [(x, pi[x]) for x in range(t)]
            assert all(f in edges for f in labels)
            actual, _ = full_square(t, t, edges)
            new = sum(labels[v] in actual[labels[u]] for u, v in combinations(range(t), 2))
            delta = -sum((b[i][k] - b[j][k]) * (b[k][i] - b[k][j])
                         for k in range(t) if k not in (i, j))
            assert new - old == delta
            switches += 1
    return switches




def reservoir_tests():
    """Explicitly extend lower cubes through an actual complete row reservoir."""
    rng = Random(181181)
    extensions = 0
    for d in range(2, 9):
        m = 1 << (d - 1)
        for j in range(1, d):
            q = m >> j
            degree = (j + 1) * q
            assert degree <= m
            b = 2 * m + d
            even = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
            odd = [x for x in range(1 << d) if x.bit_count() % 2 == 1]
            e0 = [x for x in even if x & ((1 << j) - 1) == 0]
            o0 = [x for x in odd if x & ((1 << j) - 1) == 0]
            assert len(e0) == len(o0) == q
            rows = {x: i for i, x in enumerate(e0)}
            rows.update({x: q + i for i, x in enumerate(x for x in even if x not in rows)})
            columns = {x: i for i, x in enumerate(o0)}
            edges = {(a, y) for a in range(q, m) for y in range(b)}
            for x in e0:
                required = {columns[x ^ (1 << bit)] for bit in range(j, d)}
                rest = list(set(range(b)) - required)
                rng.shuffle(rest)
                neighbours = required | set(rest[:degree - len(required)])
                assert len(neighbours) == degree
                edges.update((rows[x], y) for y in neighbours)
            # Private odd vertices each have exactly one neighbour in E0.
            for x in e0:
                for bit in range(j):
                    z = x ^ (1 << bit)
                    assert z not in columns
                    used = set(columns.values())
                    choices = [y for y in range(b) if (rows[x], y) in edges and y not in used]
                    assert choices
                    columns[z] = min(choices)
            for z in odd:
                if z not in columns:
                    columns[z] = min(set(range(b)) - set(columns.values()))
            assert len(set(rows.values())) == m
            assert len(set(columns.values())) == m
            assert all((rows[x], columns[x ^ (1 << bit)]) in edges
                       for x in even for bit in range(d))
            extensions += 1
    # Independent lower/full injective counts check the factorial multiplicity.
    for d, j, a, b in ((2, 1, 3, 4), (3, 1, 5, 5), (3, 2, 5, 5)):
        m = 1 << (d - 1)
        q = m >> j
        r, degree = m - q, (j + 1) * q
        for _ in range(16):
            edges = {(x, y) for x in range(a) for y in range(b)
                     if x < r or rng.randrange(4) != 0}
            high = [x for x in range(r, a)
                    if sum((x, y) in edges for y in range(b)) >= degree]
            renumber = {x: i for i, x in enumerate(high)}
            h = {(renumber[x], y) for x, y in edges if x in renumber}
            small = injective_count(len(high), b, h, q, q, cube_bipartite(d - j))
            large = injective_count(a, b, edges, m, m, cube_bipartite(d))
            multiplicity = falling(r, r) * falling(j * q, j * q) * falling(b - degree, m - degree)
            assert large >= small * multiplicity
    # Independently test the original-edge and FULL-square bookkeeping.
    for _ in range(128):
        a, b = 6, 7
        b0 = set(range(5))
        reservoir = {0, 1}
        degree = 4
        edges = {(x, y) for x in range(a) for y in range(b) if rng.randrange(2)}
        edges.update(product(reservoir, b0))
        high = {x for x in range(a) if x not in reservoir
                and sum((x, y) in edges for y in b0) >= degree}
        h = {(x, y) for x, y in edges if x in high and y in b0}
        _, s = full_square(a, b, edges)
        _, sh = full_square(a, b, h)
        u, r = b - len(b0), len(reservoir)
        budget_e = u * a + r * len(b0) + (degree - 1) * (a - r)
        budget_s = u * a + r * len(b0) + (degree - 2) * max(0, a - r - 1)
        assert len(edges) - len(h) <= budget_e
        assert s - sh <= budget_s * len(edges)
    return extensions

def algebra_tests():
    # The polynomial certifying t >= N^2/512 for every N >= 128.
    for x in (0, 1, 2, 17, 128, 10**6, 10**50):
        n = 128 + x
        assert n**3 - 70*n**2 + 70*n - 2 == x**3 + 314*x*x + 31302*x + 959230
        e_lower = F(n * (n - 1), 8)
        t_lower = 2 * e_lower**3 / n**4 - F(n - 1, 8)
        assert t_lower >= F(n*n, 512)
    for m in (2, 3, 4, 100, 2**32, 2**100):
        n = 128 * m
        gap = F(n*n, 64) - F(n-1, 2) - 2 * (m-2) * (n-1)
        assert gap == F(900*m - 7, 2) > 0
        n = 1024 * m
        assert F(n*n, 512) - (m-2) * (n-1) >= F(n*n, 1024)
    # Every omitted Q_(d-1) edge needs TWO original cube edges.
    for d in range(2, 101):
        m = 1 << (d-1)
        missing_aux = (d-1)*m//2 - (m-1)
        missing_original = d*m - (3*m-2)
        assert missing_original == 2 * missing_aux == (d-3)*m + 2


def main():
    spec = Path(__file__).with_name("Spec.lean")
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == SPEC_SHA256
    total, deletions, prisms = exhaustive_small()
    extra_tests()
    switches = switching_tests()
    extensions = reservoir_tests()
    algebra_tests()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == before
    print(f"PASS: {total} exhaustive bipartite hosts; {deletions} individual original-edge deletions.")
    print(f"PASS: full-square peeling budgets and link capacities; {prisms} small greedy prism audits.")
    print("PASS: paired-colour rectangle floor, energy increments, degree/codegree stability.")
    print("PASS: exact injective cut-counting bounds for C4 and 256 four-by-four Q3 tests.")
    print("PASS: all prism edges and distinct original endpoints in complete-host tests up to 32 source vertices.")
    print(f"PASS: {switches} actual-rectangle matching switches and their exact variation formula.")
    print(f"PASS: {extensions} explicit reservoir dimension-extensions (all cube edges checked), 48 count-multiplicity tests, and 128 square-budget tests.")
    print("PASS: all-dimensional constants independently reduced to positive polynomials; omitted cube-edge counts.")
    print("NOT ASSERTED: critical cube-free comparison, completion of tree prisms to cubes, or R(Q_d)=O(2^d).")
    print(f"Spec.lean unchanged: {before}")


if __name__ == "__main__":
    main()
