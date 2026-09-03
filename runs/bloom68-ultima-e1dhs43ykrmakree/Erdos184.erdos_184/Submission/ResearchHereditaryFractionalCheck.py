#!/usr/bin/env python3
"""Exact checks for ResearchHereditaryFractional.md (standard library only).

No LP solver, random graph search, or floating-point optimum is used.
Circuits and integer optima are reconstructed from the complete binary code.
Fractional values are certified by exact primal/dual pairs, against EVERY
circuit contained in the restriction. Large-parameter sampling checks only
check the proved formulas; they do not enumerate those large matroids.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, product
from math import comb
from pathlib import Path
import json

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def check_spec():
    assert sha256(Path(__file__).with_name("Spec.lean").read_bytes()).hexdigest() == SPEC_SHA256


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def xor_all(xs):
    out = 0
    for x in xs:
        out ^= x
    return out


def rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            p = v.bit_length()
            if p not in pivots:
                pivots[p] = v
                break
            v ^= pivots[p]
    return len(pivots)


def span(basis):
    words = {0}
    for b in basis:
        words |= {w ^ b for w in words}
    return words


def null_basis(columns):
    """Binary kernel basis as ground-set masks, with no symbolic package."""
    pivots, answer = {}, []
    for i, v in enumerate(columns):
        mask = 1 << i
        while v:
            p = v.bit_length()
            if p not in pivots:
                pivots[p] = (v, mask)
                break
            a, b = pivots[p]
            v ^= a
            mask ^= b
        if not v:
            answer.append(mask)
    return answer


def columns_of_rows(rows, m):
    return [sum(((row >> e) & 1) << j for j, row in enumerate(rows))
            for e in range(m)]


class BinaryCode:
    def __init__(self, basis, m):
        self.m, self.E = m, (1 << m) - 1
        self.words = sorted(span(basis), key=lambda w: (w.bit_count(), w))
        assert self.E in self.words
        self.dimension = rank(basis)
        assert len(self.words) == 1 << self.dimension
        # Independently construct a column representation of the original
        # matroid, not just its dual/cycle-code presentation.
        dual_columns = columns_of_rows(basis, m)
        parity_rows = null_basis(dual_columns)
        self.columns = columns_of_rows(parity_rows, m)
        assert rank(self.columns) == m - self.dimension
        assert xor_all(self.columns) == 0
        assert span(null_basis(self.columns)) == set(self.words)

        self.circuits = []
        for w in self.words[1:]:
            if not any(c & w == c for c in self.circuits):
                self.circuits.append(w)
        self.circuit_set = set(self.circuits)
        by_edge = [[c for c in self.circuits if c >> e & 1] for e in range(m)]
        self.minimum, self.maximum, self.partition = {0: 0}, {0: 0}, {0: ()}
        for w in self.words[1:]:
            first = (w & -w).bit_length() - 1
            choices = [c for c in by_edge[first] if c & w == c]
            assert choices
            best = min(choices, key=lambda c: self.minimum[w ^ c])
            self.minimum[w] = 1 + self.minimum[w ^ best]
            self.maximum[w] = 1 + max(self.maximum[w ^ c] for c in choices)
            self.partition[w] = (best,) + self.partition[w ^ best]
        assert all(xor_all(self.columns[e] for e in bits(w)) == 0 for w in self.words)

    def contained_circuits(self, w):
        return [c for c in self.circuits if c & w == c]

    def certificate(self, w, primal, dual, value):
        value = Q(value)
        loads = [Q(0)] * self.m
        for c, x in primal.items():
            assert c in self.circuit_set and c & w == c and x >= 0
            for e in bits(c):
                loads[e] += x
        assert loads == [Q((w >> e) & 1) for e in range(self.m)]
        assert sum(primal.values(), Q(0)) == value
        assert all(e in range(self.m) and (w >> e & 1) for e in dual)
        for c in self.contained_circuits(w):
            assert sum((dual.get(e, Q(0)) for e in bits(c)), Q(0)) <= 1
        assert sum(dual.values(), Q(0)) == value


def clique_data(n):
    edges = list(combinations(range(n), 2))
    stars = [sum(1 << e for e, uv in enumerate(edges) if v in uv) for v in range(n)]
    cuts = span(stars[:-1])
    full = (1 << len(edges)) - 1
    assert full not in cuts
    balanced = []
    for subset in combinations(range(n), n // 2):
        s = set(subset)
        balanced.append(sum(1 << e for e, (u, v) in enumerate(edges) if (u in s) != (v in s)))
    return edges, stars, cuts, balanced


class SynchronizedCliques:
    """Cycle space: direct sum of t K_n cut spaces, plus one global 1."""
    def __init__(self, n, t):
        assert n >= 5 and t >= 1
        self.n, self.t = n, t
        self.edges, self.stars, self.cuts, self.balanced = clique_data(n)
        self.m = len(self.edges)
        self.block = (1 << self.m) - 1
        self.L = (n - 1) * (n - 2) // 2
        self.U = n * n // 4
        self.alpha, self.beta = Q(n, n - 2), Q(n - 1, self.U)
        self.basis = [s << (i * self.m) for i in range(t) for s in self.stars[:-1]]
        self.basis.append((1 << (t * self.m)) - 1)
        self.code = BinaryCode(self.basis, t * self.m)
        assert self.U <= self.L
        assert self.code.dimension == t * (n - 1) + 1
        assert len(set(self.code.columns)) == t * self.m and 0 not in self.code.columns
        self.old_partition = tuple(self.stars[0] << (i * self.m) for i in range(t))
        self.old_partition += (self.code.E ^ xor_all(self.old_partition),)
        assert xor_all(self.old_partition) == self.code.E
        assert sum(c.bit_count() for c in self.old_partition) == t * self.m
        assert all(c in self.code.circuit_set for c in self.old_partition)

    def classify(self, w):
        local = [(w >> (i * self.m)) & self.block for i in range(self.t)]
        if all(x in self.cuts for x in local):
            return 0, local, [i for i, x in enumerate(local) if x]
        assert all((self.block ^ x) in self.cuts for x in local)
        return 1, local, [i for i, x in enumerate(local) if x == self.block]

    def expected_value(self, w):
        kind, _, active = self.classify(w)
        if not kind:
            return Q(len(active))
        if len(active) == self.t:
            return self.alpha
        return 1 + len(active) * self.beta

    def witnesses(self, w):
        kind, local, active = self.classify(w)
        primal, dual = Counter(), {}
        if not kind:
            for i in active:
                c = local[i] << (i * self.m)
                primal[c] += Q(1)
                dual[next(bits(c))] = Q(1)
            return primal, dual, Q(len(active))

        k = len(active)
        base = xor_all(local[i] << (i * self.m) for i in range(self.t) if i not in active)
        mass = self.alpha if k == self.t else Q(1)
        for centers in product(range(self.n), repeat=k):
            c = base
            for i, v in zip(active, centers):
                c |= (self.block ^ self.stars[v]) << (i * self.m)
            primal[c] += mass / (self.n ** k)
        if k == self.t:
            dual = {e: Q(1, self.t * self.L) for e in bits(w)}
            return primal, dual, self.alpha

        for i in active:
            for cut in self.balanced:
                primal[cut << (i * self.m)] += self.beta / len(self.balanced)
            dual.update({i * self.m + e: Q(1, self.U) for e in range(self.m)})
        frozen = next(i for i in range(self.t) if i not in active)
        anchor = frozen * self.m + next(bits(local[frozen]))
        dual[anchor] = 1 - Q(k * self.L, self.U)  # May be strictly NEGATIVE.
        return primal, dual, 1 + k * self.beta

    def audit(self, all_certificates=True):
        predicted_circuits = set()
        fractional_values = {}
        for w in self.code.words:
            kind, local, active = self.classify(w)
            is_circuit = (not kind and len(active) == 1) or (kind and not active)
            if is_circuit:
                predicted_circuits.add(w)
            count = len(active) + kind
            assert self.code.minimum[w] == self.code.maximum[w] == count
            value = self.expected_value(w)
            fractional_values[w] = value
            if all_certificates or w == self.code.E:
                self.code.certificate(w, *self.witnesses(w))
            else:
                # This branch is used only for t=1, where all proper nonzero
                # words are actual circuits, with cost exactly one.
                assert self.t == 1 and (w == 0 or w in self.code.circuit_set)
                assert value == int(w != 0)
        assert predicted_circuits == self.code.circuit_set
        p = self.alpha if self.t == 1 else Q(self.t)
        assert max(fractional_values.values()) == p
        assert self.code.minimum[self.code.E] == self.t + 1
        assert len(self.code.circuits) == self.t * ((1 << (self.n - 1)) - 1) + \
            ((1 << (self.n - 1)) - 1) ** self.t
        # Every pair of ground elements lies in an explicitly chosen global
        # star-complement circuit. This checks connectedness, not graph
        # connectedness of the bookkeeping K_n's.
        for e, f in combinations(range(self.t * self.m), 2):
            choices = []
            for i in range(self.t):
                forbidden = set()
                for h in (e, f):
                    if h // self.m == i:
                        forbidden.update(self.edges[h % self.m])
                v = next(v for v in range(self.n) if v not in forbidden)
                choices.append((self.block ^ self.stars[v]) << (i * self.m))
            c = xor_all(choices)
            assert c in self.code.circuit_set and c >> e & 1 and c >> f & 1
        return fractional_values, {
            "n": self.n, "t": self.t, "elements": self.t * self.m,
            "rank": self.t * self.m - self.code.dimension,
            "Eulerian_restrictions": len(self.code.words),
            "circuits": len(self.code.circuits), "c": self.t + 1,
            "cf": str(self.alpha), "Fmax": str(p),
            "all_fractional_certificates": all_certificates,
        }


def verify_r10_identification(model):
    assert (model.n, model.t) == (5, 1)
    cols = [1 << i for i in range(5)] + [
        (1 << i) | (1 << ((i - 1) % 5)) | (1 << ((i + 1) % 5)) for i in range(5)]
    permutation = [0, 1, 4, 5, 2, 9, 8, 7, 3, 6]
    mapped = {sum(1 << permutation[e] for e in bits(w)) for w in model.code.words}
    assert mapped == span(null_basis(cols))
    # Direct-sum additivity gives a strict ceiling counterexample.
    p, c = 3 * model.alpha, 3 * model.code.minimum[model.code.E]
    assert (p, c) == (5, 6)
    return {"clique_edge_to_R10_coordinate": permutation, "three_R10_copies_c": c,
            "three_R10_copies_Fmax": str(p)}


def verify_f7_minor(n, t, contracted, retained):
    """Prove a dual F7 minor by rank: quotient is simple rank 3 on 7 points."""
    edges, stars, _, _ = clique_data(n)
    m = len(edges)
    rows = [s << (i * m) for i in range(t) for s in stars[:-1]] + [(1 << (t * m)) - 1]
    cols = columns_of_rows(rows, t * m)
    index = {(i, *uv): i * m + e for i in range(t) for e, uv in enumerate(edges)}
    cc, rr = [cols[index[e]] for e in contracted], [cols[index[e]] for e in retained]
    d = len(cc)
    assert rank(cols) == t * (n - 1) + 1
    assert rank(cc) == d and len(rr) == 7 and rank(cc + rr) == d + 3
    assert all(rank(cc + [x]) == d + 1 for x in rr)
    assert all(rank(cc + [x, y]) == d + 2 for x, y in combinations(rr, 2))
    # The other columns are deleted. The seven remaining quotient points
    # are all nonzero elements of F_2^3, so this is precisely F7.
    return {"n": n, "t": t, "contracted": contracted, "retained": retained}


def sampling_formula(n, t, p):
    alpha = Q(n, n - 2)
    beta = Q(n - 1, n * n // 4)
    return p * (1 - p) * t + p + beta * p * p * t - \
        p ** (t + 1) * (1 + beta * t - alpha)


def fixed_size_formula(n, t, s):
    q = t + 1
    if s == q:
        return Q(n, n - 2)
    beta = Q(n - 1, n * n // 4)
    return Q(s * (q + 1 - s), q) + beta * Q(s * (s - 1), q)


def verify_sampling(model, values):
    n, t, q = model.n, model.t, model.t + 1
    by_size = Counter()
    for mask in range(1 << q):
        w = xor_all(model.old_partition[i] for i in bits(mask))
        by_size[mask.bit_count()] += values[w]
    for s in range(q + 1):
        assert by_size[s] / comb(q, s) == fixed_size_formula(n, t, s)
    for p in (Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)):
        expected = sum((v * p ** s * (1 - p) ** (q - s) for s, v in by_size.items()), Q(0))
        assert expected == sampling_formula(n, t, p)
    return {"n": n, "t": t, "fair_coin_expectation": str(sampling_formula(n, t, Q(1, 2)))}



def verify_dual_f7_star_minor():
    """M_6 has an F7 minor: its dual has the following F7* minor."""
    n = 6
    edges, stars, _, _ = clique_data(n)
    cols = columns_of_rows(stars[:-1] + [(1 << len(edges)) - 1], len(edges))
    index = {uv: e for e, uv in enumerate(edges)}
    contracted = [(0, 1), (2, 3)]
    retained = [(0, 4), (1, 4), (0, 5), (1, 5), (2, 4), (3, 4), (2, 5)]
    cc, rr = [cols[index[e]] for e in contracted], [cols[index[e]] for e in retained]
    assert rank(cc) == 2 and rank(cc + rr) == 6
    deps = [w for w in range(128) if rank(cc + [xor_all(rr[e] for e in bits(w))]) == 2]
    assert len(deps) == 8 and sorted(w.bit_count() for w in deps) == [0] + [4] * 7
    basis = []
    for w in deps:
        if rank(basis + [w]) > len(basis):
            basis.append(w)
    assert len(basis) == 3
    assert set(columns_of_rows(basis, 7)) == set(range(1, 8))
    return {"n": 6, "t": 1, "dual_minor": "F7*", "contracted": contracted,
            "retained": retained, "nonzero_cycle_weights": [4] * 7}


def verify_sampling_limits():
    results = []
    for t in (10, 100, 1000):
        n, q = t * t + 5, t + 1
        alpha, beta = Q(n, n - 2), Q(n - 1, n * n // 4)
        assert beta < Q(4, n) and 1 + beta * t - alpha >= 0
        scores = [fixed_size_formula(n, t, s) for s in range(q + 1)]
        best = max(scores)
        bound = max(alpha, Q((q + 1) ** 2, 4 * q) + beta * q)
        assert best <= bound
        assert best / q <= Q(1, 4) + Q(1, 2 * q) + Q(1, 4 * q * q) + beta
        # Independent common-p laws are mixtures of these fixed-size laws.
        fair = sampling_formula(n, t, Q(1, 2))
        assert fair <= best and fair <= Q(t, 4) + 1 + beta * t
        results.append({"t": t, "n": n, "q_over_best_exchangeable_expectation":
                        str(Q(q, 1) / best), "best_size": scores.index(best),
                        "formula_only_not_enumerated": True})
    return results


def audit_cographic_complete_bipartite(a, b):
    edges = [(u, a + v) for u in range(a) for v in range(b)]
    m, n = len(edges), a + b
    stars = [sum(1 << e for e, uv in enumerate(edges) if v in uv) for v in range(n)]
    code = BinaryCode(stars[:-1], m)  # Cut space is the cographic cycle space.
    L, alpha = (a - 1) * (b - 1) + 1, Q(a * b, (a - 1) * (b - 1) + 1)
    full_primal = Counter()
    for u in range(a):
        for v in range(a, n):
            S = (set(range(a)) - {u}) | {v}
            c = sum(1 << e for e, (x, y) in enumerate(edges) if (x in S) != (y in S))
            assert c.bit_count() == L
            full_primal[c] += Q(1, L)
    values = {}
    for w in code.words:
        if w == code.E:
            value = alpha
            code.certificate(w, full_primal, {e: Q(1, L) for e in range(m)}, value)
        else:
            # Every proper cut is either a bond, or has just its disjoint
            # individual vertex-stars as contained bonds.
            contained = code.contained_circuits(w)
            assert set(contained) == set(code.partition[w])
            assert code.minimum[w] == code.maximum[w] == len(contained)
            value = Q(len(contained))
            code.certificate(w, {c: Q(1) for c in contained},
                             {next(bits(c)): Q(1) for c in contained}, value)
        values[w] = value
    assert code.minimum[code.E] == 2
    assert max(values.values()) == max(Q(a - 1), Q(b - 1), alpha)
    return {"a": a, "b": b, "Eulerian_restrictions": len(values),
            "c": 2, "cf": str(alpha), "Fmax": str(max(values.values()))}


def main():
    check_spec()
    result = {"critical_family": [], "synchronized_family": [], "sampling_small": []}
    for n in (5, 6, 7, 8, 9, 10, 12):
        model = SynchronizedCliques(n, 1)
        values, row = model.audit(all_certificates=(n <= 8))
        result["critical_family"].append(row)
        if n == 5:
            result["R10"] = verify_r10_identification(model)
        print(f"Critical M_{n}: ALL {len(values)} Eulerian restrictions classified; c=2, Fmax={model.alpha}.", flush=True)
    for n, t in ((5, 2), (6, 2), (5, 3)):
        model = SynchronizedCliques(n, t)
        values, row = model.audit(all_certificates=True)
        if (n, t) == (5, 2):
            assert model.code.columns == [2044, 2035, 21, 26, 2047, 1, 2, 4, 8, 16,
                                          224, 800, 1344, 1664, 32, 64, 128, 256, 512, 1024]
            row["explicit_binary_columns"] = model.code.columns
        result["synchronized_family"].append(row)
        result["sampling_small"].append(verify_sampling(model, values))
        assert model.code.minimum[model.code.E] == model.code.maximum[model.code.E] == t + 1
        assert max(values.values()) == t < t + 1  # Connected ceiling counterexample.
        print(f"Synchronized M_({n},{t}): ALL {len(values)} exact LP certificates; EVERY partition has {t+1} circuits.", flush=True)
    result["nonregularity_minors"] = [
        verify_f7_minor(7, 1,
            [(0, 0, 1), (0, 1, 2), (0, 3, 4), (0, 5, 6)],
            [(0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 3, 5), (0, 3, 6)]),
        verify_f7_minor(5, 2,
            [(0, 0, 1), (0, 2, 3), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 4)],
            [(1, 1, 2), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 1, 4), (0, 2, 4), (0, 3, 4)]),
    ]
    result["nonregularity_minors"].append(verify_dual_f7_star_minor())
    print("Explicit dual F7/F7* minors: passed (nonregularity is certified).", flush=True)
    result["sampling_asymptotic_formula_checks"] = verify_sampling_limits()
    result["cographic_complete_bipartite"] = [audit_cographic_complete_bipartite(a, b)
                                              for a in range(3, 6) for b in range(3, 6)]
    print("Cographic K_(a,b), 3<=a,b<=5: all 1568 Eulerian restrictions certified.", flush=True)
    # Exact arithmetic sanity checks of the all-n length inequality and limit.
    for n in range(5, 1002):
        L, m = (n - 1) * (n - 2) // 2, n * (n - 1) // 2
        assert max(n * n // 4, m - (n - 1)) == L
        assert Q(2) / Q(n, n - 2) == 2 - Q(4, n)
    check_spec()
    print(json.dumps(result, indent=2, sort_keys=True))
    print("ALL EXACT CHECKS PASSED. Spec SHA-256 unchanged: " + SPEC_SHA256)
    print("No finite universal K, and no unbounded c/Fmax counterexample, is claimed.")


if __name__ == "__main__":
    main()
