# Finite certificate results — partial, not Erdős–Turán

`FiniteCertificate.lean` imports only `FormalConjecturesUtil`. It does not import
or modify `Submission/Spec.lean` or `Submission/Reduction.lean`.

All names below are in `Erdos28.FiniteCertificate`. The finite results have type

```lean
(A : Set ℕ) → (∀ n ≤ N, n ∈ A + A) → ∃ n, K < AdditiveCombinatorics.sumRep A n
```

| K | N (inclusive coverage endpoint) | Theorem | Tree nodes |
|---|---|---|---:|
| 2 | 5 | `cap2_obstruction` | 5 |
| 3 | 11 | `cap3_obstruction` | 22 |
| 4 | 46 | `cap4_obstruction` | 1,765 |
| 5 | 60 | `cap5_obstruction` | 33,595 |

These exclude **global ordered** representation caps. The violating sum is not
claimed to be at most `N`. For example, the terminal cap-2 check uses sum 6 while
the coverage endpoint is 5. There is no result here for K ≥ 6, no uniform-K
argument, and no proof or disproof of the asymptotic Erdős–Turán conjecture.
Optimality witnesses from the JSON files are not formalized or claimed here.

## Generic proof interface

- `repCount_eq_sumRep`: the executable finite count equals the genuine ordered
  `sumRep` of the bit-mask set.
- `Matches`, `Matches.omit`, `Matches.include`: a mask is exactly an arbitrary
  set's prefix, and the two chronological membership decisions preserve this.
- `omit_count_pos`, `count_le_of_matches`: connect coverage and the global cap
  of the arbitrary ambient set to the finite numeric tests.
- `check_sound`: structural induction on any accepted finite binary tree rules
  out an ambient set with the matching prefix, coverage through `N`, and global
  ordered cap `K`.
- `obstruction_of_check`: root version, giving the displayed existential result.
- `checkFragment_sound`: verified composition of smaller proof-carrying blocks.
  Each graft carries a previously proved checker equality and has its exact
  chronological state checked. No unchecked external reference is accepted.
- `cap2_checked` through `cap5_checked`: acceptance of the complete certificates.

Every missing omit edge has count zero at the next integer. Every missing
include edge has an explicit sum with count exceeding K. All kept edges are
checked recursively, so no admissible branch is omitted. The checker may also
accept redundant inadmissible branches; it never relies on the generator's
claims of admissibility.

## Verification commands

From `/workspace/leanproject` (Lean 4.27.0 / Mathlib):

```sh
# Full kernel check, including the #print axioms audits:
lake env lean -DwarningAsError=true Submission/FiniteCertificate.lean

# To also build and run the small regression tests:
mkdir -p .lake/build/lib/lean/Submission
lake env lean -DwarningAsError=true \
  -o .lake/build/lib/lean/Submission/FiniteCertificate.olean \
  Submission/FiniteCertificate.lean
lake env lean -DwarningAsError=true Submission/FiniteCertificateTests.lean

# Optional deterministic regeneration; not needed for compilation:
python3 Submission/generate_finite_certificate.py

# Independent Python audit of the source JSON certificates:
python3 /tmp/et_cap_descent/verify_certificates.py
```

All numerical proofs use `decide +kernel` (ordinary `decide` in small tests).
There is no native decision procedure, admitted proof, or added axiom.
All audited theorem dependencies lie in
`{propext, Classical.choice, Quot.sound}`.

The generated data retain every decision node. To avoid a monolithic large
kernel reduction, caps 4 and 5 use respectively 14 and 265 private verified
blocks, assembled by `checkFragment_sound`. Generated checks are elaborated
synchronously (`Elab.async false`) to avoid retaining many pending proof states.
The generator is untrusted; its output must pass all Lean checks. The source
JSON SHA-256 hashes are recorded next to the public certificate definitions.

Verified reference run: the complete warning-as-error build exited 0 in about
295 seconds (about 6.9 GiB peak RSS); the regression tests exited 0 in 4.2 seconds.
All 21 printed axiom audits passed the whitelist above. All four requested
finite caps are verified; none is left as an unchecked computation.

Regression tests check ordered-pair multiplicity, rejected premature leaves,
incorrect witnesses, shorter horizons, larger caps, incorrect graft states,
and the exact four public theorem types.
