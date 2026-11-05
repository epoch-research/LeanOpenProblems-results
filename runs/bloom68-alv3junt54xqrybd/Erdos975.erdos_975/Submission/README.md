# Erdős 975: verified partial formalization

**The requested proof/disproof is not complete.** `Spec.lean` retains both
original statements, its original import, and both original admissions. No
proof or disproof claim has been submitted.

## Completed supporting results

All mathematical helpers are in `Erdos975Support` and are independent of the
admitted original theorems.

- `RootMeanGeneral.lean`: positive linear residue-root means for every
  nonconstant irreducible integer polynomial, including nonmonic cases; the
  full original divisor-average conclusion in degrees one and two.
- `DivisorPairing.lean` and `BalancedReduction.lean`: exact divisor pairing
  with the overlap correction, valid even at zero.
- `RootReciprocalAverage.lean`: small-divisor means from the linear root mean.
- `PolynomialSetup.lean` and `RealCutoff.lean`: exact original floor-sum
  compatibility, finite-head correction, and natural/real cutoff transfer.
- `OverlapEstimate.lean`: high-degree overlap is negligible even compared
  with the input cutoff.
- `ConjectureReduction.lean`: exact equivalence between the unrestricted
  conjecture and finite high-degree balanced-divisor limits.
- `IntrinsicReduction.lean`: exact intrinsic-cutoff correction, a monotone
  nonnegative central summatory function, the equivalent high-degree limit,
  universal strictly positive normalized lower bounds, and the independent
  exact-negation reduction. None of these asserts high-degree convergence.

## Exact unresolved Lean assertion

With `open Filter Polynomial Erdos975Support` and `open scoped Topology`, the
remaining sufficient and necessary assertion is:

```lean
∀ f : ℤ[X], 3 ≤ f.natDegree → Irreducible f →
  (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
  ∃ L : ℝ, Tendsto
    (fun N : ℕ ↦ intrinsicBalancedAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 L)
```

A finite limit of any value suffices. The predicted value is not needed.
Monotonicity, positivity, and bounds alone do not establish this assertion.
A disproof instead requires one actual admissible high-degree polynomial
for which this normalized mean has no finite limit; no such polynomial has
been proved here.

## Reproducible checks

From `/workspace/leanproject`:

```sh
lake build Submission.RootMeanGeneralAudit Submission.RootMeanGeneralRegression \
  Submission.ConjectureReduction Submission.IntrinsicReduction \
  Submission.KrylovCertificateAudit Submission.KrylovCertificateRegression \
  Submission.Spec
```

The two `Spec.lean` admission warnings remain and are expected for this
**incomplete** state. All other Lean files are admission-free. The supporting
axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.

Current integrity hash of the unchanged specification:

```text
da4dfe02e9dcc63b39f7148a83024b91410547b0051e3ee8b727e0d9d1f1ebb3
```
