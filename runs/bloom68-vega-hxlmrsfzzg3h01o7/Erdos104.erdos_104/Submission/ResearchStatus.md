# Erdős 104 — unresolved research checkpoint

Neither theorem in `Submission/Spec.lean` has been proved. That file is unchanged,
and both original `sorry`s remain. No proof/disproof claim has been submitted.

## Verified Lean results

`Submission/Prelim.lean` is independent of the specification and contains no
`sorry`. Its 32 audited declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. In particular it proves:

- The qualifying unit-circle set is finite.
- The supremum defining the maximum is attained by an actual configuration.
- `3 * unitCircleCount P ≤ P.card * (P.card - 1)`.
- The same inequality for the maximum at cardinality `n`.
- The conjecture is equivalent to
  ```lean
  ∀ K : ℕ, ∃ N : ℕ, ∀ P : Finset ℝ²,
    N ≤ P.card → K * unitCircleCount P ≤ P.card ^ 2
  ```
- Its negation is equivalent to
  ```lean
  ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, ∃ P : Finset ℝ²,
    N ≤ P.card ∧ P.card ^ 2 < K * unitCircleCount P
  ```

These equivalences prove neither side. The quadratic upper bound does not imply
little-o, and the known subset-sum examples have only order `n^(3/2)` circles.

## Verification

From `/workspace/leanproject`:

```sh
lake env lean Submission/Prelim.lean
lake env lean -o .lake/build/lib/lean/Submission/Prelim.olean Submission/Prelim.lean
lake env lean /tmp/Erdos104PrelimAudit.lean
lake env lean Submission/Spec.lean
```

The last command succeeds **with two sorry warnings**, so it is not evidence of
a completed submission. The audit file and its output are
`/tmp/Erdos104PrelimAudit.lean` and `/tmp/Erdos104PrelimAudit.log`.

Unchanged specification SHA-256:

```text
486f86eb50acb7aaf2523279794aaec87d40c5fb3a5c86d5445d18265b35aee5
```

## Principal mathematical gap

No unconditional mechanism has been established that excludes a fixed positive
quadratic density of distinct triple points in arbitrary unit-circle arrangements.
No actual family with such density has been constructed either.

The research notes below are **not Lean proofs**. Their exact computational checks
do not fill this gap:

- `/tmp/unit_circle_density_gap/collapsing_dense_arrangements.md`: reduction to
  finite analytic unit motions with quadratically many marked points collapsing.
- `/tmp/unit_circle_web_reaudit/LOCAL_THEOREM_AUDIT.md`: local analytic web
  obstruction; finite density has not been shown to supply such a web.
- `/tmp/unit_circle_family_inverse/compatibility_algebra.md` and
  `/tmp/unit_circle_reconstruction/algebraic_lift_second_jet.md`: scalar
  interpolation and conditional motion-encoding results. Actual normal velocity
  data have not been converted to the required bounded-complexity scalar data.
- `/tmp/unit_circle_phase_removal/result.md`: a useful deletion theorem for an
  already exactly balanced partition. Constructing the required partition from
  density remains unproved.
- `/tmp/unit_circle_arrangement_inverse/findings.md`: planar localization of
  actual stresses. Bounded local stresses do not themselves obstruct collapse;
  shared-center gluing remains essential.
- `/tmp/unit_circle_functional_rank_density/findings.md`: a fixed-density
  **non-unit** countermodel shows that the extracted additive/rank properties
  alone do not imply bounded functional rank. It is not a disproof of Erdős104.
- `/tmp/unit_circle_valuation_density/findings.md`: weighted valuation-grid
  bounds, a genuine unit example with large leading-coordinate multiplicities,
  and an explicitly **non-unit** dense leading-data model. Neither exact balance
  nor the required multiscale bound follows.

The nearby published results inspected in the corpus require additional
hypotheses: three prescribed pencils (arXiv:1407.6625), anchored spatial circles
(arXiv:2003.02190), or pre-existing foliations (arXiv:2108.07311). Those hypotheses
have not been derived for this specification.

Do not replace a target `sorry` with a conditional transfer, an unproved inverse
statement, a finite numerical check, or a theorem from a restricted configuration
class. A genuine new mathematical argument is still needed before submission.
