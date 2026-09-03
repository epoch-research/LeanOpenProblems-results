# Checkpoint: moving Type-I complete; conjecture still unresolved

`Spec.lean` has not been changed. No complete proof or irrational counterexample
has been found. Do not submit the current `Spec.lean` as a completed proof.

New compiled files:

- `WeightedBeattyRows.lean`: weighted output-arc discrepancy; the input/output
  logarithm replacement costs at most `log Q * (1 + log Q)`. Main theorem:
  `Erdos972WeightedBeattyRows.logRow_output_approx`.
- `RealLogCenter.lean`: common real scalar
  `D(y) = sum_{q ≤ y} log q Λ(q) - (log y - 1) ψ(y)`.
  Proves `D(y)/y → 0` from qualitative PNT, and uniform common-endpoint error
  bounded by `24 * (1 + log y)^2`.
- `MovingCenteredRows.lean`: centered logarithmic row differs from
  `D(y)/β` by at most `3 log y * E + 25 (1 + log y)^2`.
  Signed reciprocal Möbius bound keeps the first Type-I common scalar bounded
  by `2 |D(αN)| / α`, with no factor depending on the moving cutoff.
- `GrowingTypeI.lean`: `exists_growing_typeI_scale` controls BOTH Type-I terms
  AND the small Vaughan term at arbitrarily large scales `N = floor(u^6 / α)`.
  Uniform over all U,V with U ≤ root64 u, V ≤ root64 u, U*V ≤ root64 u.
  Error is ≤ εN. This completes the plan in the preceding context summary.
- `GrowingTypeIIReduction.lean`: exact correlation reduction with those moving
  cutoffs, and a counterexample obstruction when
  `U = V = growingCutoff u = sqrt(root64 u)` (~N^(1/768)).
  `finite_primeSet_forces_growing_negative_typeII` says any counterexample
  forces `|B/N + 1| ≤ ε` at arbitrarily large common good scales, with both
  cutoffs arbitrarily large.
  `infinite_primeSet_of_growing_typeII_gap` gives a sufficient strict gap
  above -N, explicitly as a hypothesis. That hypothesis is NOT proved.

`PolynomialRowScales.lean` now also contains the strengthened theorem
`exists_polynomial_beatty_arc_scale_root64`, which returns the equality
`v = root64 u`. The original theorem has been preserved as a wrapper.

All of the above principal results compile and print only the axioms
`propext`, `Classical.choice`, and `Quot.sound`.

The genuine two-prime Type-II estimate remains unresolved. One-prime row
cancellation, upper-bound sieves, almost-everywhere results, and growing
Type-I cutoffs do not by themselves give the required prime-pair lower bound.
