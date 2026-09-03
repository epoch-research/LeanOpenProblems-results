#!/usr/bin/env python3
"""Exact audit of the Frobenius two-fiber Z/6 construction (no dependencies).

All triples are multisets: repeated summands are deliberately retained.
F_q elements are bit-packed polynomials; K is F_q[T]/(T^3+T+w).
For each q=2,8,32, audit every w making this normalized cubic irreducible.
These w cover all degree-three theta up to F_q-affine changes and conjugacy
for *within-composition fiber sizes*, not for the pure-branch cross fibers.
The parity-triangle obstruction itself works for every theta, without any
normalization.  Run from any directory; results are written beside the script.
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement
from math import comb, gcd
from pathlib import Path
import argparse
import json


class BaseField:
    MODULI = {1: 0b11, 3: 0b1011, 5: 0b100101}

    def __init__(self, m):
        self.m = m
        self.q = 1 << m
        self.modulus = self.MODULI[m]
        self.mul = [[self.multiply_raw(a, b) for b in range(self.q)]
                    for a in range(self.q)]
        self.square = [self.mul[a][a] for a in range(self.q)]
        self.sqrt = [0] * self.q
        for a, b in enumerate(self.square):
            self.sqrt[b] = a
        self.inverse = [0] * self.q
        for a in range(1, self.q):
            inverses = [b for b in range(1, self.q) if self.mul[a][b] == 1]
            assert len(inverses) == 1, "Base modulus is not irreducible"
            self.inverse[a] = inverses[0]
        assert sorted(self.square) == list(range(self.q))

    def multiply_raw(self, a, b):
        c = 0
        while b:
            if b & 1:
                c ^= a
            b >>= 1
            a <<= 1
            if a & self.q:
                a ^= self.modulus
        return c

    def div(self, a, b):
        assert b
        return self.mul[a][self.inverse[b]]

    def trace(self, a):
        result = 0
        for _ in range(self.m):
            result ^= a
            a = self.square[a]
        assert result in (0, 1)
        return result

    def normalized_irreducibles(self):
        image = {self.mul[self.square[x]][x] ^ x for x in range(self.q)}
        return [w for w in range(1, self.q) if w not in image]


class CubicField:
    def __init__(self, base, w):
        self.base = base
        self.q = base.q
        self.w = w
        assert w in base.normalized_irreducibles()
        # Encoding h0 + q*h1 + q^2*h2 is also a bit packing.
        self.coefficients = [(x % self.q, (x // self.q) % self.q,
                              x // (self.q * self.q))
                             for x in range(self.q ** 3)]
        self.theta = self.q

    def pack(self, coefficients):
        a, b, c = coefficients
        return a + self.q * b + self.q * self.q * c

    def mul(self, x, y):
        a0, a1, a2 = self.coefficients[x]
        b0, b1, b2 = self.coefficients[y]
        M = self.base.mul
        d0 = M[a0][b0]
        d1 = M[a0][b1] ^ M[a1][b0]
        d2 = M[a0][b2] ^ M[a1][b1] ^ M[a2][b0]
        d3 = M[a1][b2] ^ M[a2][b1]
        d4 = M[a2][b2]
        # theta^3=theta+w, theta^4=theta^2+w*theta.
        return self.pack((d0 ^ M[self.w][d3],
                          d1 ^ d3 ^ M[self.w][d4], d2 ^ d4))

    def power(self, x, n):
        result = 1
        while n:
            if n & 1:
                result = self.mul(result, x)
            x = self.mul(x, x)
            n >>= 1
        return result

    def check(self):
        q, w = self.q, self.w
        assert self.power(self.theta, 3) == self.theta ^ w
        assert self.power(self.theta, q) != self.theta
        assert self.power(self.theta, q ** 3) == self.theta
        for t in range(q):
            assert self.power(self.theta ^ t, q ** 3 - 1) == 1
            assert self.mul(self.theta ^ t, self.theta ^ t) == self.pack(
                (self.base.square[t], 0, 1))


def mask_of(triple):
    mask = 0
    for point in triple:
        mask ^= 1 << point
    return mask


def serialize_triple(triple, q):
    return [[point // q, point % q] for point in triple]


def serialize_fiber(key, triples, field):
    k, output = key
    return {"branch1_count_mod3": k,
            "field_coefficients_h0_h1_h2": list(field.coefficients[output]),
            "triples": [serialize_triple(t, field.q) for t in triples]}


def histogram(fibers):
    return {str(k): v for k, v in sorted(Counter(map(len, fibers.values())).items())}


def linear_system(rows):
    """Rank and consistency of mask.dot(epsilon)=1 for all collision pairs."""
    basis = {}
    inconsistent = False
    for original_mask in rows:
        mask, rhs = original_mask, 1
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (mask, rhs)
                break
            old_mask, old_rhs = basis[pivot]
            mask ^= old_mask
            rhs ^= old_rhs
        if not mask and rhs:
            inconsistent = True
    rank = len(basis)
    return {"equation_count": len(rows), "coefficient_rank": rank,
            "augmented_rank": rank + int(inconsistent),
            "consistent": not inconsistent}


def mixed21_from_cubic(output, field):
    """Independently reconstruct the entire 2+1 fiber via its cubic in c^2.

    For f=T^3+T+w, A=h2+1, B=h1+w, C=h0.  The cubic is
    (z+1)(z^2+A*z+C)+B*w=0.  The exceptional denominator z=1
    is treated explicitly; quadratic splitting includes double roots.
    """
    base, q, w = field.base, field.q, field.w
    M, sq = base.mul, base.square
    h0, h1, h2 = field.coefficients[output]
    A, B, C = h2 ^ 1, h1 ^ w, h0
    result = []
    for z in range(q):
        if M[z ^ 1][sq[z] ^ M[A][z] ^ C] ^ M[B][w]:
            continue
        if z != 1:
            s = base.div(B, z ^ 1)
        else:
            assert B == 0
            s = base.div(C ^ 1 ^ A, w)
        p = A ^ z
        if s == 0:
            roots = [base.sqrt[p]]
        else:
            trace_splits = base.trace(base.div(p, sq[s])) == 0
            roots = [a for a in range(q) if sq[a] ^ M[s][a] ^ p == 0]
            assert bool(roots) == trace_splits
            assert len(roots) in (0, 2)
        if roots:
            a = min(roots)
            b = a ^ s
            assert a <= b
            result.append((a, b, q + base.sqrt[z]))
    return sorted(result)


def parity_certificate(field, triple_info, fibers):
    """Three individually necessary inequalities whose XOR is 0=1."""
    q = field.q
    if q > 2:
        pairs = [((a, a, q + b), (b, b, q + a))
                 for a, b in [(0, 1), (1, 2), (0, 2)]]
        kind = "uniform repeated-branch0 triangle"
    else:
        # theta^3=theta+1; every degree-three theta over F2 is equivalent
        # to this one by translation and Frobenius.
        pairs = [((0, 0, 0), (2, 2, 3)),
                 ((0, 0, 3), (1, 1, 2)),
                 ((0, 1, 1), (2, 3, 3))]
        kind = "q=2 mixed/pure triangle"
    rows = []
    xor_mask = 0
    for left, right in pairs:
        key = triple_info[left]
        assert left != right and key == triple_info[right]
        assert left in fibers[key] and right in fibers[key]
        mask = mask_of(left) ^ mask_of(right)
        xor_mask ^= mask
        row = serialize_fiber(key, [left, right], field)
        row["epsilon_variables"] = [[i // q, i % q]
                                    for i in range(2 * q) if mask >> i & 1]
        row["rhs"] = 1
        rows.append(row)
    assert xor_mask == 0 and len(rows) % 2 == 1
    return {"kind": kind, "equations": rows, "xor_lhs": 0, "xor_rhs": 1}


def trace_graph_prediction(base, w):
    """Check the nondegenerate trace form underlying the exact fiber formulas.

    B(x,y)=Tr(w*(x^2*y+x*y^2+x^2*y^2)).  Three-element fibers
    correspond to edges (one singleton parameter is 1) and triangles
    (no singleton parameter is 1) in its orthogonality graph on Fq*.
    The proof, including the double-root cases for F2, is in the note.
    """
    q, M, sq = base.q, base.mul, base.square
    form = [[base.trace(M[w][M[sq[x]][y] ^ M[x][sq[y]] ^ M[sq[x]][sq[y]]])
             for y in range(q)] for x in range(q)]
    assert all(form[x][y] == form[y][x] for x in range(q) for y in range(q))
    assert all(any(form[x]) for x in range(1, q)), "Trace form must have zero radical"
    isotropic = [x for x in range(1, q) if form[x][x] == 0]
    anisotropic = [x for x in range(1, q) if form[x][x] == 1]
    n, r = q // 2, q // 2 - 1
    assert len(isotropic) == r and len(anisotropic) == n
    degree = {x: sum(form[x][y] == 0 for y in range(1, q) if y != x)
              for x in range(1, q)}
    assert all(degree[x] == r - 1 for x in isotropic)
    assert all(degree[x] == r for x in anisotropic)
    edges = sum(form[x][y] == 0 for x, y in combinations(range(1, q), 2))
    triangles = sum(form[x][y] == form[x][z] == form[y][z] == 0
                    for x, y, z in combinations(range(1, q), 3))
    assert edges == r * r and triangles == comb(r, 3)
    predictions = {1: q * (5 * q * q + 4 * q + 4) // 16,
                   2: q * q * (q + 2) // 16,
                   3: q * (q * q - 4) // 48}
    assert predictions[3] == edges + triangles
    return {"histogram_prediction": {str(k): v for k, v in predictions.items() if v},
            "nonzero_isotropic_vectors": len(isotropic),
            "anisotropic_vectors": len(anisotropic),
            "orthogonality_edges": edges,
            "orthogonality_triangles": triangles,
            "radical_is_zero": True}


def classify_two_fibers(fibers, field):
    """Verify the five disjoint cases in the proof of the N2 formula."""
    base, q, w = field.base, field.q, field.w
    M, sq = base.mul, base.square
    counts = Counter()
    for output, triples in fibers.items():
        if len(triples) != 2:
            continue
        h0, h1, h2 = field.coefficients[output]
        A, B, C = h2 ^ 1, h1 ^ w, h0
        roots = [z for z in range(q)
                 if M[z ^ 1][sq[z] ^ M[A][z] ^ C] ^ M[B][w] == 0]
        if len(roots) == 3:
            key = "three_roots_including_1" if 1 in roots else "three_roots_excluding_1"
        else:
            assert len(roots) == 2
            # The derivative is z^2+A+C, identifying the double root.
            doubles = [z for z in roots if sq[z] ^ A ^ C == 0]
            assert len(doubles) == 1
            a = base.sqrt[doubles[0]]
            b = base.sqrt[next(z for z in roots if z != doubles[0])]
            key = ("double_root_1" if a == 1 else "single_root_1" if b == 1
                   else "two_roots_excluding_1")
        counts[key] += 1
    n, r = q // 2, q // 2 - 1
    expected = {"three_roots_excluding_1": n * r * (r - 1) // 2,
                "three_roots_including_1": n * r,
                "double_root_1": q - 1,
                "single_root_1": r,
                "two_roots_excluding_1": r * (r - 1)}
    assert all(counts[k] == v for k, v in expected.items())
    assert sum(counts.values()) == q * q * (q + 2) // 16
    return expected


def audit(m, w, verify_all_outputs=False):
    base = BaseField(m)
    field = CubicField(base, w)
    field.check()
    q = base.q
    assert gcd(6, q ** 3 - 1) == 1
    values = [field.theta ^ t for t in range(q)]
    values += [field.mul(z, z) for z in values]
    pairs = {(a, b): field.mul(values[a], values[b])
             for a, b in combinations_with_replacement(range(2 * q), 2)}
    fibers = defaultdict(list)
    composition_fibers = [defaultdict(list) for _ in range(4)]
    triple_info = {}
    for triple in combinations_with_replacement(range(2 * q), 3):
        a, b, c = triple
        k = sum(point // q for point in triple)
        output = field.mul(pairs[a, b], values[c])
        assert output != 0
        key = (k % 3, output)
        fibers[key].append(triple)
        composition_fibers[k][output].append(triple)
        triple_info[triple] = key
    assert len(triple_info) == comb(2 * q + 2, 3)
    for k in (0, 3):
        assert len(composition_fibers[k]) == comb(q + 2, 3)
        assert max(map(len, composition_fibers[k].values())) == 1
    for k in (1, 2):
        assert sum(map(len, composition_fibers[k].values())) == q * comb(q + 1, 2)
    # Reconstruct the mixed 2+1 fibers by an algebraically different method.
    # --all-outputs also checks that every unoccupied output has no solutions.
    outputs_to_verify = (range(1, q ** 3) if verify_all_outputs
                         else composition_fibers[1])
    for output in outputs_to_verify:
        reconstructed = mixed21_from_cubic(output, field)
        assert reconstructed == sorted(composition_fibers[1].get(output, [])), (
            m, w, output, reconstructed, composition_fibers[1].get(output, []))
    assert max(map(len, composition_fibers[1].values())) <= 3
    rows = [mask_of(a) ^ mask_of(b) for fiber in fibers.values()
            for a, b in combinations(fiber, 2)]
    system = linear_system(rows)
    assert not system["consistent"]
    certificate = parity_certificate(field, triple_info, fibers)
    graph_prediction = trace_graph_prediction(base, w)
    assert histogram(composition_fibers[1]) == graph_prediction["histogram_prediction"]
    result = {"m": m, "q": q, "base_modulus_binary": bin(base.modulus),
              "theta_minpoly": {"u": 0, "v": 1, "w": w},
              "total_unordered_triples_with_repetition": len(triple_info),
              "composition_histograms": {
                  str(k): histogram(composition_fibers[k]) for k in range(4)},
              "mod3_histograms": {
                  str(k): histogram({v: ts for (r, v), ts in fibers.items() if r == k})
                  for k in range(3)},
              "parity_system": system,
              "inconsistency_certificate": certificate,
              "trace_orthogonality_graph": graph_prediction,
              "mixed21_two_fiber_classification": classify_two_fibers(composition_fibers[1], field),
              "mixed21_cubic_verified_outputs": len(outputs_to_verify),
              "mixed21_all_nonzero_outputs_verified": verify_all_outputs,
              "maximum_mixed_fiber_examples": {},
              "repeated_pair_3_fiber_count": 0,
              "repeated_pair_3_fiber_example": None}
    for k in (1, 2):
        output, triples = max(composition_fibers[k].items(), key=lambda kv: len(kv[1]))
        result["maximum_mixed_fiber_examples"][str(k)] = serialize_fiber(
            (k, output), triples, field)
    for a, b in combinations(range(q), 2):
        triple = (a, a, q + b)
        key = triple_info[triple]
        if len(fibers[key]) == 3:
            result["repeated_pair_3_fiber_count"] += 1
            if result["repeated_pair_3_fiber_example"] is None:
                result["repeated_pair_3_fiber_example"] = serialize_fiber(key, fibers[key], field)
    assert result["repeated_pair_3_fiber_count"] == graph_prediction["orthogonality_edges"]
    if q == 2:
        good = []
        for epsilon in range(1 << (2 * q)):
            # Direct CRT-tag triple sums, not just Gaussian elimination.
            tags = [next(tag for tag in range(6)
                         if tag % 3 == i // q and tag % 2 == (epsilon >> i & 1))
                    for i in range(2 * q)]
            products = [(sum(tags[i] for i in t) % 6, triple_info[t][1])
                        for t in triple_info]
            if len(set(products)) == len(products):
                good.append(epsilon)
        assert not good
        result["exhaustive_epsilon_vectors_tested"] = 1 << (2 * q)
        result["strong_B3_epsilon_vectors"] = good
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-outputs", action="store_true",
                        help="verify the cubic at every nonzero field output, including empty fibers")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    results = []
    for m in (1, 3, 5):
        base = BaseField(m)
        ws = base.normalized_irreducibles()
        assert len(ws) == (base.q + 1) // 3
        for w in ws:
            result = audit(m, w, verify_all_outputs=args.all_outputs)
            results.append(result)
            print(f"q={base.q:2} w={w:2} "
                  f"mixed21={result['composition_histograms']['1']} "
                  f"mixed12={result['composition_histograms']['2']} "
                  f"pure_cross={result['mod3_histograms']['0'].get('2', 0)} "
                  f"rank={result['parity_system']['coefficient_rank']} "
                  f"consistent={result['parity_system']['consistent']}", flush=True)
    payload = {"description": "Frobenius two-fiber Z6 exact audit; repeated triples included",
               "field_encoding": "Fq bit-polynomials; K coordinates h0+h1*theta+h2*theta^2",
               "composition_histogram_keys": "k=number of branch1 summands; values count output fibers by size",
               "normalization_scope": "Affine theta normalization preserves within-composition fibers, not pure cross fibers",
               "audits": results}
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(f"Wrote {len(results)} audits to {args.output}")


if __name__ == "__main__":
    main()
