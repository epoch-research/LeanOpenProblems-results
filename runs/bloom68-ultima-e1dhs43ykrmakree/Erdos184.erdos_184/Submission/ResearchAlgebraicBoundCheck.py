#!/usr/bin/env python3
"""Focused exact checks for ResearchAlgebraicBound.md.

No graph catalogue, random tests, LP, or conjectured count bound is used.
All arithmetic is integral or Fraction. No files are written.

Run from the project root:
  PYTHONDONTWRITEBYTECODE=1 python3 Submission/ResearchAlgebraicBoundCheck.py
"""

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import factorial, prod
from pathlib import Path


@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple

    def __post_init__(self):
        assert tuple(sorted(set(self.edges))) == self.edges
        assert all(0 <= u < v < self.n for u, v in self.edges)
        assert all(d % 2 == 0 for d in self.degrees())

    def degrees(self):
        d = [0] * self.n
        for u, v in self.edges:
            d[u] += 1
            d[v] += 1
        return d

    @property
    def full(self):
        return (1 << len(self.edges)) - 1


def from_cycles(n, cycles):
    edges = []
    for cycle in cycles:
        assert len(cycle) >= 3 and len(set(cycle)) == len(cycle)
        edges.extend(tuple(sorted((u, v)))
                     for u, v in zip(cycle, cycle[1:] + cycle[:1]))
    assert len(edges) == len(set(edges)), "input cycles must be edge-disjoint"
    return Graph(n, tuple(sorted(edges)))


def bouquet(q, isolates=0):
    return from_cycles(2 * q + 1 + isolates,
                       [[0, 2 * i + 1, 2 * i + 2] for i in range(q)])


def simple_cycles(g):
    """Enumerate undirected vertex-simple cycles, once up to reversal."""
    adj = [[] for _ in range(g.n)]
    for i, (u, v) in enumerate(g.edges):
        adj[u].append((v, i))
        adj[v].append((u, i))
    found = {}
    for start in range(g.n):
        def dfs(path, vertices, edges):
            for v, eid in adj[path[-1]]:
                if v == start:
                    if len(path) >= 3 and path[1] < path[-1]:
                        mask = edges | (1 << eid)
                        assert mask not in found
                        found[mask] = vertices
                elif v > start and not (vertices >> v) & 1:
                    dfs(path + [v], vertices | (1 << v), edges | (1 << eid))
        dfs([start], 1 << start, 0)
    return tuple(sorted(found.items()))


def partitions(g, cycles):
    by_edge = [[] for _ in g.edges]
    for i, (mask, _) in enumerate(cycles):
        for e in range(len(g.edges)):
            if (mask >> e) & 1:
                by_edge[e].append(i)

    @lru_cache(None)
    def solve(mask):
        if not mask:
            return ((),)
        e = (mask & -mask).bit_length() - 1
        out = []
        for i in by_edge[e]:
            cmask = cycles[i][0]
            if cmask & mask == cmask:
                out.extend((i,) + tail for tail in solve(mask ^ cmask))
        return tuple(out)

    out = tuple(frozenset(d) for d in solve(g.full))
    assert len(set(out)) == len(out)
    assert out, "an even graph must have a simple-cycle partition"
    for d in out:
        mask = 0
        for i in d:
            assert not mask & cycles[i][0]
            mask |= cycles[i][0]
            degree = Counter(v for e, uv in enumerate(g.edges)
                             if cycles[i][0] >> e & 1 for v in uv)
            assert set(degree.values()) == {2}
            assert sum(1 << v for v in degree) == cycles[i][1]
        assert mask == g.full
    return out


def add(p, q):
    ans = [Fraction(0)] * max(len(p), len(q))
    for i, a in enumerate(p):
        ans[i] += a
    for i, a in enumerate(q):
        ans[i] += a
    while len(ans) > 1 and not ans[-1]:
        ans.pop()
    return tuple(ans)


def scale(p, a):
    return tuple(a * c for c in p)


def linear_times(p, a, b):
    """Multiply p(s) by a + b*s."""
    return add((*(a * c for c in p), 0),
               (0, *(b * c for c in p)))


def sparse_product(a, b):
    """Multiplication in a commuting square-zero-generator algebra."""
    out = defaultdict(Fraction)
    for x, c in a.items():
        for y, d in b.items():
            if not x & y:
                out[x | y] += c * d
    return {x: c for x, c in out.items() if c}


def determinant(g, vertex_variables=False):
    """Direct permutation expansion of det(I-A) or det(I-YA).

    The low m bits are edge variables. In the second case the next n
    bits are commuting square-zero vertex variables. This procedure
    does not use the simple-cycle enumeration.
    """
    m = len(g.edges)
    rows = [[(i, None)] for i in range(g.n)]
    for eid, (u, v) in enumerate(g.edges):
        rows[u].append((v, eid))
        rows[v].append((u, eid))
    out = Counter()

    def visit(i, columns, mask, coefficient):
        if i == g.n:
            out[mask] += coefficient
            return
        for j, eid in rows[i]:
            if columns >> j & 1:
                continue
            factor = 0 if eid is None else 1 << eid
            if eid is not None and vertex_variables:
                factor |= 1 << (m + i)
            if mask & factor:
                continue
            inversions = (columns >> (j + 1)).bit_count()
            sign = -1 if (inversions + (eid is not None)) % 2 else 1
            visit(i + 1, columns | (1 << j), mask | factor,
                  coefficient * sign)

    visit(0, 0, 0, 1)
    assert out[0] == 1
    return {mask: c for mask, c in out.items() if c}


def determinant_power_coefficient(g):
    """[x_E] det(I-A)^s, using the finite binomial series."""
    delta = determinant(g)
    nilpotent = {mask: c for mask, c in delta.items() if mask}
    power = {0: Fraction(1)}
    binomial = (Fraction(1),)
    answer = (Fraction(0),)
    for k in range(len(g.edges) // 3 + 1):
        answer = add(answer, scale(binomial, power.get(g.full, 0)))
        power = sparse_product(power, nilpotent)
        binomial = scale(linear_times(binomial, -k, 1), Fraction(1, k + 1))
    return answer


def chromatic_polynomial(n, edges):
    """Exact inclusion-exclusion sum over edge subsets."""
    ans = [0] * (n + 1)
    for mask in range(1 << len(edges)):
        parent = list(range(n))
        components = n

        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v

        for e, (u, v) in enumerate(edges):
            if mask >> e & 1:
                u, v = root(u), root(v)
                if u != v:
                    parent[u] = v
                    components -= 1
        ans[components] += (-1) ** mask.bit_count()
    return tuple(ans)


def chromatic_sum(cycles, decompositions):
    answer = (0,)
    for d in decompositions:
        ordered = sorted(d)
        edges = [(a, b) for a, b in combinations(range(len(d)), 2)
                 if cycles[ordered[a]][1] & cycles[ordered[b]][1]]
        chi = chromatic_polynomial(len(d), edges)
        answer = add(answer, scale(chi, (-2) ** len(d)))
    return answer


def local_pairings(items):
    if not items:
        return ((),)
    first = items[0]
    out = []
    for j in range(1, len(items)):
        rest = items[1:j] + items[j + 1:]
        out.extend(((first, items[j]),) + tail for tail in local_pairings(rest))
    return tuple(out)


def transition_polynomials(g):
    """Independent enumeration of all local transition systems.

    A circuit is accepted as vertex-simple only if its actual edge
    subgraph has degree two at every used original vertex.
    """
    incidence = [[] for _ in range(g.n)]
    for e, uv in enumerate(g.edges):
        for v in uv:
            incidence[v].append(e)
    circuit_poly, simple_poly = Counter(), Counter()
    for choices in product(*(local_pairings(tuple(a)) for a in incidence)):
        parent = list(range(len(g.edges)))

        def root(e):
            while parent[e] != e:
                e = parent[e]
            return e

        for pairs in choices:
            for e, f in pairs:
                parent[root(e)] = root(f)
        groups = defaultdict(list)
        for e in range(len(g.edges)):
            groups[root(e)].append(e)
        circuit_poly[len(groups)] += 1
        if all(set(Counter(v for e in group for v in g.edges[e]).values()) == {2}
               for group in groups.values()):
            simple_poly[len(groups)] += 1
    expected = prod(prod(range(1, d, 2)) for d in g.degrees())
    assert sum(circuit_poly.values()) == expected
    return circuit_poly, simple_poly


def nilpotent_encoding(g, cycles):
    """Verify -1/2 log det(I-YA) and the projection-before-exp identity."""
    delta = determinant(g, vertex_variables=True)
    nilpotent = {mask: c for mask, c in delta.items() if mask}
    power = {0: Fraction(1)}
    logarithm = defaultdict(Fraction)
    for k in range(1, g.n // 3 + 1):
        power = sparse_product(power, nilpotent)
        for mask, c in power.items():
            logarithm[mask] += Fraction((-1) ** k, 2 * k) * c
    logarithm = {mask: c for mask, c in logarithm.items() if c}
    expected = {emask | (vmask << len(g.edges)): Fraction(1)
                for emask, vmask in cycles}
    assert logarithm == expected
    reset = defaultdict(Fraction)
    for mask, c in logarithm.items():
        reset[mask & g.full] += c
    power = {0: Fraction(1)}
    before_exp = Counter()
    for k in range(len(g.edges) // 3 + 1):
        value = power.get(g.full, Fraction(0)) / factorial(k)
        if value:
            assert value.denominator == 1
            before_exp[k] = value.numerator
        power = sparse_product(power, reset)
    # Exponentiating before the vertex reset is generally the wrong operation.
    power = {0: Fraction(1)}
    after_exp = Counter()
    for k in range(g.n // 3 + 1):
        value = sum((c for mask, c in power.items() if mask & g.full == g.full),
                    Fraction(0)) / factorial(k)
        if value:
            assert value.denominator == 1
            after_exp[k] = value.numerator
        power = sparse_product(power, logarithm)
    return before_exp, after_exp


def stability_restrictions(cycles, decompositions):
    """Check the factorization used by the general non-stability proof."""
    checks = 0
    for d, e in combinations(decompositions, 2):
        common, left, right = d & e, d - e, e - d
        adjacency = {i: set() for i in left | right}
        for i in left:
            for j in right:
                if cycles[i][0] & cycles[j][0]:
                    adjacency[i].add(j)
                    adjacency[j].add(i)
        todo, components = set(adjacency), []
        while todo:
            stack, component = [min(todo)], set()
            while stack:
                i = stack.pop()
                if i not in component:
                    component.add(i)
                    stack.extend(adjacency[i] - component)
            todo -= component
            a, b = component & left, component & right
            assert len(a) >= 2 and len(b) >= 2
            components.append((a, b))
        predicted = set()
        for choices in product((0, 1), repeat=len(components)):
            selected = set(common)
            for component, side in zip(components, choices):
                selected |= component[side]
            predicted.add(frozenset(selected))
        allowed = set(d | e)
        restricted = {f for f in decompositions if f <= allowed}
        assert restricted == predicted
        x, y = sorted(components[0][0])[:2]
        bivariate = Counter((int(x in f), int(y in f)) for f in restricted)
        k = 2 ** (len(components) - 1)
        assert bivariate == {(0, 0): k, (1, 1): k}
        assert -k * k < 0  # Rayleigh difference of k*(1+x*y).
        checks += 1
    return checks


def as_counter(p):
    assert all(Fraction(c).denominator == 1 for c in p)
    return Counter({i: int(c) for i, c in enumerate(p) if c})


def format_poly(p, symbol="t"):
    return " + ".join(str(c) if k == 0 else f"{c}*{symbol}^{k}"
                      for k, c in sorted(p.items())) or "0"


def protected_snapshot(root):
    allowed = {"ResearchAlgebraicBound.md", "ResearchAlgebraicBoundCheck.py"}
    return {str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest()
            for directory in (root / "Submission", root / "newSubmission")
            for p in directory.rglob("*")
            if p.is_file() and not (p.parent == root / "Submission"
                                   and p.name in allowed)}


def main():
    root = Path(__file__).resolve().parents[1]
    protected = protected_snapshot(root)
    spec_hash = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"
    assert sha256((root / "Submission" / "Spec.lean").read_bytes()).hexdigest() == spec_hash
    graphs = {
        "empty": Graph(0, ()),
        "isolates": Graph(4, ()),
        "triangle": from_cycles(3, [[0, 1, 2]]),
        "hexagon": from_cycles(6, [list(range(6))]),
        "two_disjoint_triangles": from_cycles(6, [[0, 1, 2], [3, 4, 5]]),
        "bowtie_plus_isolate": bouquet(2, isolates=1),
        "three_triangle_bouquet": bouquet(3),
        "three_triangle_chain": from_cycles(7, [[0, 1, 2], [2, 3, 4], [4, 5, 6]]),
        "four_triangle_bouquet": bouquet(4),
        "K5": Graph(5, tuple(combinations(range(5), 2))),
    }
    results = {}
    total_transitions = total_stability = 0
    for name, g in graphs.items():
        cycles = simple_cycles(g)
        decompositions = partitions(g, cycles)
        z = Counter(map(len, decompositions))
        f = determinant_power_coefficient(g)
        assert f == chromatic_sum(cycles, decompositions)
        r = as_counter(tuple(c * Fraction(-1, 2) ** k for k, c in enumerate(f)))
        independent_r, independent_z = transition_polynomials(g)
        assert r == independent_r and z == independent_z
        assert all(r[k] >= z[k] for k in z)
        encoded_z, wrong_order = nilpotent_encoding(g, cycles)
        assert encoded_z == z
        if max(g.degrees(), default=0) > 2:
            assert not wrong_order
        else:
            assert wrong_order == z
        total_transitions += sum(r.values())
        total_stability += stability_restrictions(cycles, decompositions)
        results[name] = f, r, z
        print(f"{name}: n={g.n}, m={len(g.edges)}, simple_cycles={len(cycles)}, "
              f"partitions={len(decompositions)}; Z={format_poly(z)}; R={format_poly(r)}")

    f1, _, z1 = results["hexagon"]
    f2, _, z2 = results["two_disjoint_triangles"]
    f3, _, z3 = results["bowtie_plus_isolate"]
    assert f3 == add(f2, scale(f1, 2))
    assert z2 == z3 == {2: 1} and z1 == {1: 1}
    assert results["K5"][1] == {1: 132, 2: 96, 3: 15}
    assert results["K5"][2] == {2: 6, 3: 15}
    assert results["three_triangle_bouquet"][1] == {1: 8, 2: 6, 3: 1}
    assert results["three_triangle_chain"][1] == {1: 4, 2: 4, 3: 1}
    assert protected == protected_snapshot(root)
    print(f"PASS: {len(graphs)} focused inputs; {total_transitions} transition systems; "
          f"{total_stability} two-partition stability restrictions.")
    print("PASS: direct determinant / chromatic identity / transition enumeration agree.")
    print("PASS: nilpotent projection-before-exponential gives the actual Z, not R.")
    print("PASS: fixed-(n,m) scalar-linear-correction obstruction checked.")
    print(f"PASS: {len(protected)} protected files unchanged; Spec SHA-256 {spec_hash}.")
    print("NO universal O(n) simple-cycle partition bound is proved by these checks.")


if __name__ == "__main__":
    main()
