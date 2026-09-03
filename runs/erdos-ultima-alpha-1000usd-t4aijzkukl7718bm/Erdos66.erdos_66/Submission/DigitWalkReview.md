# Threshold-walk candidate and two-sided repair review

## Original task status

The original conjecture remains unproved and undisproved. Spec.lean is
unchanged, and no proof has been submitted.

## Explicit digit candidate examined

For a binary word b_0,...,b_(k-1), put

    S_i = sum_(j<i) (2*b_j-1).

Choose an integer threshold h and one of two orientations. Replace each
zero bit by the base-four digit 0; replace each one bit by digit 1 or 2
according to which side of h its walk height S_i lies on, reversing the
choice for the other orientation. The union over thresholds and orientations
was considered as a possible sparse set.

Its apparent attraction was the order of its finite counting function:
the number of different threshold colorings of a typical word is on the
order of sqrt(k). This heuristic suggested the desired sqrt(N log N)
scale. Two special target families also had small representation counts
linear in k in the finite computations.

It fails structurally. Extreme thresholds retain every number whose base-four
digits are all 0 or 2. At the target consisting of k digits all equal to 2,
every such k-digit word has a digitwise complementary partner. There are
2^k ordered representations, while the target's logarithm is at most
k log 4. No numerical asymptotic inference is needed for this rejection.

## Checked formal obstruction

DigitCoreExplore.lean defines recursively

    core(0) = {0},
    core(k+1) = 4*core(k) union (4*core(k)+2),
    center(0) = 0,
    center(k+1) = 4*center(k)+2.

It proves:

* card_core: |core(k)| = 2^k;
* core_reflection: a in core(k) implies center(k)-a in core(k);
* core_peak: core(k) subset A implies r_A(center(k)) >= 2^k;
* center_bounds: k <= center(k) < 4^k;
* core_excludes_finite_limit: containing every core(k) precludes a finite
  logarithmically normalized representation limit at any real c.

The last proof uses the elementary inequality k^2 <= 2^k for k >= 4, so
there is no appeal to experimental growth. The file compiles and has a built
olean. DigitCoreAxiomCheck.lean audits the two principal results.

This is NOT a negation of the original existential statement. It excludes
only sets containing this particular digital core.

## Two-sided correction review

The existing LocalMovesExplore identities allow deletions and insertions:
one moved point changes any target count by at most two, with an exact
formula for the collateral changes and for aggregate squared-error change.
No improving-move selection theorem or convergence argument was found.

A small change per move is not a bound on the accumulated error, and a
small aggregate squared error is not a uniform o(log n) estimate. Neither
can be promoted to the missing infinite-set construction without another
argument.
