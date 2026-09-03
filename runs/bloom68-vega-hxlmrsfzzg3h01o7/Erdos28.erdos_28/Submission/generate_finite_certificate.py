#!/usr/bin/env python3
"""Reify ET finite-cap JSON trees as kernel-checked Lean certificate data.

This generator is NOT trusted. FiniteCertificate.lean proves soundness of the
Boolean checker and of proof-carrying grafts. Each small generated block must
pass `decide +kernel`; every graft includes a previously proved checker result.
Splitting the tree avoids a single very large kernel reduction. The JSON files
and independent verifier are in /tmp/et_cap_descent/.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
BEGIN = "/- BEGIN GENERATED FINITE CERTIFICATES -/"
END = "/- END GENERATED FINITE CERTIFICATES -/"


def reify(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    assert data["format"] == "ordered-cap-prefix-tree-v1"
    cap = data["cap"]
    horizon = data["max_covered"] + 1
    nodes = data["nodes"]
    seen = set()
    parts = []

    def tree(ident, expected_n, expected_mask):
        term = unchunked_tree(ident, expected_n, expected_mask)
        # This is a syntactic size limit, not a search cutoff: the subtree
        # is retained, proved, and grafted back with its proof and exact state.
        if len(term) > 1500:
            name = f"cap{cap}Part{len(parts)}"
            block = name + "Block"
            parts.append(f"private def {block} : Fragment {cap} {horizon} :=\n  {term}\n\n"
                         f"private def {name} : Certificate := {block}.toCertificate\n\n"
                         f"private theorem {name}_checked : check {cap} {horizon} "
                         f"{expected_n} {expected_mask} {name} = true :=\n"
                         f"  checkFragment_sound {block} {expected_n} {expected_mask} "
                         f"(by decide +kernel)\n")
            return f"(.graft {expected_n} {expected_mask} {name} {name}_checked)"
        return term

    def unchunked_tree(ident, expected_n, expected_mask):
        assert 0 <= ident < len(nodes) and ident not in seen
        seen.add(ident)
        n, mask, omit, include = nodes[ident]
        assert (n, mask) == (expected_n, expected_mask)
        assert 1 <= n <= horizon and 0 < mask < 1 << n and mask & 1
        elems = [a for a in range(n) if mask >> a & 1]
        reps = Counter(a + b for a in elems for b in elems)
        assert max(reps.values()) <= cap
        assert all(reps[s] > 0 for s in range(n))
        cand = elems + [n]
        inc_reps = Counter(a + b for a in cand for b in cand)
        assert (omit >= 0) == (reps[n] > 0)
        assert (include >= 0) == (max(inc_reps.values()) <= cap)
        if omit >= 0:
            left = tree(omit, n + 1, mask)
        if include >= 0:
            right = tree(include, n + 1, mask | (1 << n))
        else:
            witness = min(s for s, r in inc_reps.items() if r > cap)
        if omit < 0 and include < 0:
            return f"(.closed {witness})"
        if omit < 0:
            return f"(.onlyInclude {right})"
        if include < 0:
            return f"(.onlyOmit {witness} {left})"
        return f"(.split {left}\n    {right})"

    term = tree(data["root"], 1, 1)
    assert len(seen) == len(nodes)
    declarations = "\n".join(parts)
    digest = hashlib.sha256(raw).hexdigest()
    return f'''\n{declarations}
private def cap{cap}Root : Fragment {cap} {horizon} :=
  {term}

/-- Reified from `{path.name}`: {len(nodes):,} nodes.
SHA-256: `{digest}`. -/
def cap{cap}Certificate : Certificate := cap{cap}Root.toCertificate

/-- Kernel computation of the complete cap-{cap} tree, in proof-carrying blocks. -/
theorem cap{cap}_checked : check {cap} {horizon} 1 1 cap{cap}Certificate = true :=
  checkFragment_sound cap{cap}Root 1 1 (by decide +kernel)

/-- **Partial finite result, not Erdős–Turán:** coverage of `0..{horizon}`
forces some global ordered representation count to exceed {cap}. -/
theorem cap{cap}_obstruction (A : Set ℕ) (hcov : ∀ n ≤ {horizon}, n ∈ A + A) :
    ∃ n, {cap} < sumRep A n :=
  obstruction_of_check {cap} {horizon} cap{cap}Certificate cap{cap}_checked A hcov

#print axioms cap{cap}_checked
#print axioms cap{cap}_obstruction
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--caps", type=int, nargs="+", default=[2, 3, 4, 5])
    parser.add_argument("--input-dir", type=Path, default=Path("/tmp/et_cap_descent"))
    parser.add_argument("--output", type=Path, default=HERE / "FiniteCertificate.lean")
    args = parser.parse_args()
    source = args.output.read_text()
    if BEGIN not in source:
        source = source.replace("end Erdos28.FiniteCertificate", BEGIN + "\n" + END +
                                "\n\nend Erdos28.FiniteCertificate")
    before, rest = source.split(BEGIN)
    _, after = rest.split(END)
    generated = "\nset_option Elab.async false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    for cap in args.caps:
        generated += reify(args.input_dir / f"cap_{cap}_certificate.json")
    args.output.write_text(before + BEGIN + generated + END + after)
    print(f"Wrote caps {args.caps} to {args.output} ({args.output.stat().st_size:,} bytes).")


if __name__ == "__main__":
    main()
