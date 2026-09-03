# Verified diagonal bound for Gaussian-prime walks

## Result

`Submission.DiagonalBound` proves

```lean
Erdos952.no_bounded_step_sequence_of_bound_le_four {C : ℤ} (hC : C ≤ 4) :
  ¬ ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C
```

It also proves `Erdos952.five_le_bound_of_witness`: any such witness must have
`5 ≤ C`. These are partial small-bound results, **not** a proof about all
constant step bounds or a solution of `Submission.Spec`.

## Proof components

- `DiagonalArithmetic.lean`: finite exceptional set given by norms 2, 5, 13;
  coordinate bounds using a finite `[-4,4] × [-4,4]` box; explicit quotients
  by `2 ± i` and `3 ± 2i`; prime congruence exclusions; parity reduction;
  zero-or-diagonal classification below norm 4; impossibility of norm 3.
- `DiagonalCertificate.lean`: an explicit potential on `Fin 65 × Fin 65`,
  with every allowed diagonal edge checked by **`decide +kernel`**.
  The sieve is `x ± 2y ≢ 0 (mod 5)`, `x ± 5y ≢ 0 (mod 13)`.
  It has 2,304 surviving residues, 4,356 directed edges and 243 components,
  with maximum component size 580 (generator statistics).
- `DiagonalBound.lean`: residue/translation and prime/sieve bridges;
  application of the existing general finite-potential theorem.
- `DiagonalBoundCheck.lean`: theorem-use examples and axiom audits.
- `generate_diagonal_certificate.py`: deterministic, **untrusted** BFS table
  generator. Lean checks the table independently; the BFS need not be trusted.

Parity is imposed on actual Gaussian integers, not on residues modulo 65.
This is why the smaller quotient is sufficient even though translation by 65
in one coordinate changes parity.

## Build and check

From the project root, using the existing compiled `FinitePotential` and
`SmallBound` modules:

```sh
python3 Submission/generate_diagonal_certificate.py  # optional regeneration
lake env lean -o .lake/build/lib/lean/Submission/DiagonalArithmetic.olean \
  Submission/DiagonalArithmetic.lean
lake env lean -o .lake/build/lib/lean/Submission/DiagonalCertificate.olean \
  Submission/DiagonalCertificate.lean
lake env lean -o .lake/build/lib/lean/Submission/DiagonalBound.olean \
  Submission/DiagonalBound.lean
lake env lean Submission/DiagonalBoundCheck.lean
```

All of these checks succeeded. Every audited theorem, including the final
obstruction and the exact certificate, has only the axioms `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or compiler-trust axiom.
The sources use neither `native_decide` nor `trustCompiler`.

Additional checks performed:

- Regeneration produces byte-identical certificate source.
- A temporary copy with the potential at `(0,1)` changed from `(0,0)` to `(0,1)`
  is rejected by Lean: `Tactic decide proved that the proposition ... is false`.
- A wrapped negative-coordinate edge is explicitly tested in the check module.
- SHA-256 comparisons confirm that `Spec.lean`, `FinitePotential.lean`, and
  `SmallBound.lean` were not changed.
