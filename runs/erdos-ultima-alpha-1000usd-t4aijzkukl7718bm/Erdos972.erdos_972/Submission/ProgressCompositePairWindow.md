# Composite-only moving-window bound — not a settlement

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No prime-pair infinitude proof or irrational counterexample has been obtained.

## Verified file

`Submission/CompositePairWindow.lean`, namespace
`Erdos972CompositePairWindow`.

For alpha>=1, t>0, N>=1 and

    t log(floor(alpha*N)) <= 1/4,

`composite_window_upper` proves

    compositePairMinorantSum(t,alpha,N) <= primePowerBudget(alpha,N).

The sum deletes every term having a prime input OR a prime output.
On retained terms the finite pointwise minorant is at most the Mangoldt
product. Only proper prime powers can contribute positively after deletion;
the existing explicit error budget bounds their total contribution. Negative
terms are not discarded or asserted absent.

For any eventually positive parameter sequence t(N) satisfying the window:

* `parameter_tendsto_zero_of_window` proves t(N)->0+.
* `moving_composite_upper` proves, for every epsilon>0, eventually

      compositePairMinorantSum(t(N),alpha,N)/N < epsilon.

  This is an upper bound, NOT a claim of convergence to zero of a signed sum.

* `moving_composite_mean_gap` proves the ACTUAL error lower bound

      N/4 < |compositePairMinorantSum(t(N),alpha,N)
             - N*pairMean(t(N))|

  eventually in N. Here pairMean is the fixed-parameter mean previously
  proved for every irrational alpha>=1, and pairMean(t)->32/63 as t->0+.

Thus the fixed-parameter theorem for the composite-only sum genuinely
cannot be transferred to this moving window. The conclusion is about
that deleted sum, not the full two-scale sum. It does not rule out a
sufficient positive moving-window estimate for the full sum; such an
estimate would have to detect prime contributions and is still unproved.

All four printed declarations compile and audit with only propext,
Classical.choice, and Quot.sound. The file has no sorry. No original
conjecture statement or import was changed, and no incomplete proof was
submitted.
