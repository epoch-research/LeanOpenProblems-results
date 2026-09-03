# Frequent square-root fluctuations

## Status

The original conjecture remains neither proved nor disproved. `Spec.lean`
is unchanged and still contains its original `sorry`.

## New checked results

`FrequentFluctuationExplore.lean` removes the extra squared-error convergence
hypothesis from the previously proved fluctuation restriction.

For any putative witness A with nonzero limiting coefficient c:

* `error_envelope_limit_lower_bound`: if an eventual upper envelope f of
  `(r_A(n)-c H_(n+1))^2` satisfies `f(n)/log(n) -> d`, then `c/2 <= d`.
* `frequently_squared_error_gt`: for every d<c/2, arbitrarily large n satisfy
  `(r_A(n)-c H_(n+1))^2/log(n) > d`.
* `frequently_abs_harmonic_error_gt`: for every a>=0 with a^2<c/2,
  `|r_A(n)-c H_(n+1)| > a sqrt(log n)` infinitely often.
* `frequently_abs_log_error_gt` and `exists_large_log_fluctuation` give the
  same assertion centered at c log(n), rather than c H_(n+1).

All declarations compile. `FrequentFluctuationAxiomCheck.lean` audits the
principal theorems; only propext, Classical.choice, and Quot.sound occur.

## Proof mechanism

The normalized weighted mass gap already tends to c/2. For an eventual
squared-error envelope f, replace it by the pointwise maximum of f and the
squared error. This only changes finitely many values, so its normalized
logarithmic limit is unchanged. Its weighted series dominates the squared
error series, and hence the mass gap. The Abelian limit forces d>=c/2.
The frequent deviation bounds follow by excluding an eventual smaller
constant envelope.

Finally H_(n+1)-log(n) tends to the Euler-Mascheroni constant, so dividing
the center difference by sqrt(log n) gives zero. This transfers every
strictly subcritical fluctuation constant to the conjecture's log center.

## Scope

These are genuine necessary conditions under the original witness
hypothesis, with no second convergence assumption. They are still fully
compatible with an error o(log n). They therefore cannot be used as a
disproof of the original existential statement, and have not been submitted
as one.
