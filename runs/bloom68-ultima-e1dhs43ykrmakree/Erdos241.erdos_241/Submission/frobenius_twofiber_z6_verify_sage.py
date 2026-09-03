#!/usr/bin/env -S sage -python
"""Independent Sage verification of frobenius_twofiber_z6_audit.json.

Uses Sage polynomial quotient fields and Sage matrix ranks, not the custom
arithmetic, reconstruction, or Gaussian elimination in the audit script.
Usage: sage -python Submission/frobenius_twofiber_z6_verify_sage.py
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json

from sage.all import GF, PolynomialRing, matrix


def hist(fibers):
    return {str(k): v for k, v in sorted(Counter(map(len, fibers.values())).items())}


def mask_of(triple):
    mask = 0
    for i in triple:
        mask ^= 1 << i
    return mask


def verify(row):
    m, q = row["m"], row["q"]
    R2 = PolynomialRing(GF(2), "B")
    B = R2.gen()
    modulus_integer = int(row["base_modulus_binary"], 2)
    modulus = sum(GF(2)((modulus_integer >> i) & 1) * B ** i for i in range(m + 1))
    assert modulus.is_irreducible()
    F = GF(2) if m == 1 else GF(q, "b", modulus=modulus)

    def fq(n):
        return F(n) if m == 1 else F.fetch_int(n)

    R = PolynomialRing(F, "X")
    X = R.gen()
    u, v, w = [row["theta_minpoly"][s] for s in ("u", "v", "w")]
    f = X ** 3 + fq(u) * X ** 2 + fq(v) * X + fq(w)
    assert f.is_irreducible()
    K = R.quotient(f, "theta")
    theta = K.gen()
    values = [theta + fq(t) for t in range(q)]
    values += [z ** 2 for z in values]
    pair_products = {(a, b): values[a] * values[b]
                     for a, b in combinations_with_replacement(range(2 * q), 2)}
    compositions = [defaultdict(list) for _ in range(4)]
    fibers = defaultdict(list)
    for triple in combinations_with_replacement(range(2 * q), 3):
        a, b, c = triple
        k = sum(i // q for i in triple)
        output = pair_products[a, b] * values[c]
        compositions[k][output].append(triple)
        fibers[k % 3, output].append(triple)
    assert {str(k): hist(compositions[k]) for k in range(4)} == row["composition_histograms"]
    assert {str(k): hist({v: ts for (r, v), ts in fibers.items() if r == k})
            for k in range(3)} == row["mod3_histograms"]
    masks = [mask_of(a) ^ mask_of(b) for ts in fibers.values()
             for a, b in combinations(ts, 2)]
    coefficient_matrix = matrix(GF(2), [[(mask >> i) & 1 for i in range(2 * q)]
                                       for mask in masks])
    augmented_matrix = coefficient_matrix.augment(matrix(GF(2), len(masks), 1, [1] * len(masks)))
    system = row["parity_system"]
    assert len(masks) == system["equation_count"]
    assert coefficient_matrix.rank() == system["coefficient_rank"]
    assert augmented_matrix.rank() == system["augmented_rank"]
    assert augmented_matrix.rank() > coefficient_matrix.rank()
    certificate = row["inconsistency_certificate"]
    xor_mask = 0
    for eq in certificate["equations"]:
        triples = [tuple(i * q + t for i, t in triple) for triple in eq["triples"]]
        h0, h1, h2 = eq["field_coefficients_h0_h1_h2"]
        output = fq(h0) + fq(h1) * theta + fq(h2) * theta ** 2
        key = eq["branch1_count_mod3"], output
        assert len(triples) == 2 and triples[0] != triples[1]
        assert all(t in fibers[key] for t in triples)
        mask = mask_of(triples[0]) ^ mask_of(triples[1])
        xor_mask ^= mask
        assert [[i // q, i % q] for i in range(2 * q) if mask >> i & 1] == eq["epsilon_variables"]
        assert eq["rhs"] == 1
    assert xor_mask == 0 and len(certificate["equations"]) % 2 == 1
    repeated_three = sum(len(fibers[1, (values[a] * values[b]) ** 2]) == 3
                         for a, b in combinations(range(q), 2))
    assert repeated_three == row["repeated_pair_3_fiber_count"] == (q - 2) ** 2 // 4
    # Independent checks of the trace-form proof and its double-root cases.
    def form(x, y):
        return int((fq(w) * (x ** 2 * y + x * y ** 2 + x ** 2 * y ** 2)).trace())
    gram = matrix(GF(2), [[form(fq(1 << i), fq(1 << j)) for j in range(m)]
                          for i in range(m)])
    assert gram.rank() == m
    ortho = [[form(fq(x), fq(y)) for y in range(q)] for x in range(q)]
    graph = row["trace_orthogonality_graph"]
    assert sum(ortho[x][x] == 0 for x in range(1, q)) == graph["nonzero_isotropic_vectors"]
    assert sum(ortho[x][y] == 0 for x, y in combinations(range(1, q), 2)) == graph["orthogonality_edges"]
    assert sum(ortho[x][y] == ortho[x][z] == ortho[y][z] == 0
               for x, y, z in combinations(range(1, q), 3)) == graph["orthogonality_triangles"]
    assert graph["histogram_prediction"] == hist(compositions[1])
    cases = Counter()
    for output, triples in compositions[1].items():
        if len(triples) != 2:
            continue
        h = output.lift()
        A, Bc, C = h[2] + 1, h[1] + fq(w), h[0]
        root_multiplicities = ((X + 1) * (X ** 2 + A * X + C) + Bc * fq(w)).roots()
        if len(root_multiplicities) == 3:
            key = ("three_roots_including_1" if any(z == 1 for z, _ in root_multiplicities)
                   else "three_roots_excluding_1")
        else:
            assert len(root_multiplicities) == 2
            double = next(z for z, multiplicity in root_multiplicities if multiplicity == 2)
            single = next(z for z, multiplicity in root_multiplicities if multiplicity == 1)
            key = ("double_root_1" if double == 1 else "single_root_1" if single == 1
                   else "two_roots_excluding_1")
        cases[key] += 1
    assert all(cases[k] == v for k, v in row["mixed21_two_fiber_classification"].items())
    for example in row["maximum_mixed_fiber_examples"].values():
        k = example["branch1_count_mod3"]
        h0, h1, h2 = example["field_coefficients_h0_h1_h2"]
        output = fq(h0) + fq(h1) * theta + fq(h2) * theta ** 2
        triples = [tuple(i * q + t for i, t in triple) for triple in example["triples"]]
        assert sorted(triples) == sorted(fibers[k, output])
    print(f"Sage independently verified q={q}, w={w}: all fibers, both ranks, and certificates", flush=True)


def main():
    path = Path(__file__).with_name("frobenius_twofiber_z6_audit.json")
    data = json.loads(path.read_text())
    for row in data["audits"]:
        verify(row)
    print(f"PASS: {len(data['audits'])} exact audits independently verified")


if __name__ == "__main__":
    main()
