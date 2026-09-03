# Review of recursive quadratic-error rounding

## Status

This review did not produce a proof or disproof of the conjecture. Spec.lean
is unchanged. No valid proof has been submitted.

## Sufficient target

The previously checked fractional profile p satisfies p*p(n)=H_(n+1).
For a Boolean rounding with e=1_A-p and prefix discrepancy o(log n), the
linear error e*p is already negligible. The sufficient condition still
missing is the POINTWISE estimate

    (e*e)(n)=o(log n).

Controlling partial sums of e, or an averaged convolution, is not enough.
The existing actual bounded-discrepancy counterexamples prohibit making
that inference universally.

## Recursive sign-pattern check

The Rudin-Shapiro recursion was examined as a potential source of quadratic
cancellation, not assumed to supply it. With P'=P+X^m Q and Q'=P-X^m Q, the
exact identities are

    P'^2 = P^2+2X^m PQ+X^(2m)Q^2,
    Q'^2 = P^2-2X^m PQ+X^(2m)Q^2,
    P'Q' = P^2-X^(2m)Q^2.

Thus square coefficients remain coupled to the mixed product PQ; a
partial-sum or Fourier-norm estimate for P alone does not close the needed
coefficient recurrence. Exact small finite integer-convolution calculations
were made to inspect this recurrence. They are diagnostics only, not a
proof of any asymptotic failure or success of Rudin-Shapiro rounding.
No uniform quadratic estimate for a sparse Boolean rounding was obtained.

## Other reviewed construction possibilities

* Recursive thinning of a dense carrier needs quantitative control of both
  the linear and quadratic errors on the SUCCESSIVE sparse carriers.
  A bound for a dense signed sequence is not such a theorem. Generic
  concentration retains a log(range)-dependent cost at the critical
  logarithmic target mean.
* A fixed periodic fine template cannot be kept as a permanent sparse
  support in a witness, by the already checked residue restrictions.
  Letting the template change restores the mixed-count compatibility gap.
* Grouping fields through nested finite extensions gives compatible field
  arithmetic only at widely separated dimensions. It does not automatically
  control the intermediate ordinary-integer prefixes or their carries.
* Point-dependent recoloring is not excluded by the fixed-routing theorem.
  However, no joint color-selection theorem with a vanishing relative
  error, while retaining prefixes and the correct density, was proved.

These are limitations of the reviewed arguments, not universal impossibility
statements. The exact original existential statement remains open in this
working development.
