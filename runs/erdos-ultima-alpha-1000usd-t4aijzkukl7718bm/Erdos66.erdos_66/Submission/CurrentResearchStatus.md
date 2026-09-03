# Current status after matching-based superquadratic completion

`Spec.lean` remains the original unresolved theorem. No submission tool has
been called. Do not replace it by any of the finite auxiliary results.

Newest complete result:
`Erdos66SuperquadraticCompletion.superquadratic_exception_completion`, with
`cubic_exception_completion`, follows from a new matching-based repair engine.
Its fourteen-file pipeline compiles, has built oleans, and passes both axiom
audits. See `MatchingRepairProgress.md` for exact statements and the remaining
gap. No base set meeting the completion hypotheses is constructed.

## Mathematical obstruction still present

The finite construction gives power annuli but not a compatible infinite set.
It uses a low cyclic period M comparable to the target scale, and high random
blocks only out to M^a, with a depending on the target accuracy. Passing to an
unrelated period leaves uncontrolled mixed counts. At a hard spatial switch,
mixed old/new pairs comprise a positive fraction of all representations, so
neither an upper bound nor ignoring a finite prefix resolves the transition.

## Further avenues reconsidered (none is a proof)

* Generic sparse quadratic rounding cannot simply invoke Spencer or a general
  matching-discrepancy theorem: for random matching systems the entropy of
  sparse assignments is too small to beat logarithmic-scale extreme tails.
* Fixed-digit products preserve a permanent low-residue bias. Filling all
  old digits removes that bias but multiplies the high-level coefficient by
  the old modulus; it does not solve the small-coefficient high-level problem.
* Cyclic variance has an RMS floor of order sqrt(mean). Random translation
  refinements combined with a union bound retain a fixed relative-error
  threshold at fixed logarithmic coefficient, rather than giving o(1).
* Coherent finite-field towers do preserve old parabolas, but subfield sizes
  jump at least quadratically. Generic new fibers are small while the old
  singular fiber is large, giving the wrong intermediate prefix profile.
  Naive carry averaging over all base-p coordinates has exponential cost.
* A hypothetical continuous flag of finite (pre)semifields is not a quick fix:
  if W is a proper subalgebra of dimension d in a division algebra V, the
  induced invertible multiplication maps on V/W force dim(V/W)>=d.
* A new parabola has O(H) mixed intersections with ANY subset of one horizontal
  line, independent of that subset's cardinality. But an old interval fits
  in one line only when its length is at most p, while the new cyclic period
  is about p^2. This bound alone leaves the same scale gap.
* Cross sums between graph templates modulo two different primes do not
  reduce to the same quadratic root-count formula; no uniform small error
  for those mixed sums has been established.
* None of the Tauberian, residue, Fourier, variance, parity, or Erdős–Fuchs
  necessary conditions obtained so far contradicts r_A(n)~c log n.

The attempted reference-page download still fails DNS resolution. No online
source or newly resolved status has been verified.

## Subsequently completed

`MixedFlatObstructionExplore.lean` proves that arbitrarily accurate cyclic
self-flatness alone gives NO uniform mixed-count bound: reflect B to obtain
C=-B, then the mixed zero count is |B|, unbounded relative to the fixed mean.
See `MixedFlatObstructionProgress.md`; its axiom check passes. This remains
an auxiliary obstruction, not a negation of the original conjecture.

## Sparse-deletion obstruction completed

`DyadicDeletionExplore.lean` shows that a set with an O(log n) representation
upper bound can be pruned at a cost O((log N)^2) below N to force holes at all
powers of two. The counting profile is unchanged. A nonzero square-root-log
counting profile then implies no representation limit exists for the pruned
set. Thus a sharp density plus an upper envelope is not a pointwise lower-bound
principle. See `DyadicDeletionProgress.md`. This is not a disproof of Erdős 66.

## Constructive global one-target repair completed

`GlobalRepairExplore.lean`, theorem `eventually_global_repair`, now repairs
any sufficiently large single target n by exactly 2m (m<=D log n), using 2m
new points in [n/4,n], while every other representation count increases by
at most epsilon log(z+2). The threshold is uniform over A with a given global
O(log n) bound. All eight new pipeline files compile. See
`GlobalRepairProgress.md` and `RepairAxiomCheck.lean`.

This is not an iteration over all targets: accumulated collateral remains
uncontrolled for a dense collection of deficits. It does not settle Spec.

## Summable clipped repairs and sparse-exception completion

`RepairChainExplore.lean` and `SparseRepairExplore.lean` now compile and
have built oleans. The latter proves `sparse_exception_completion`: for
fixed c>0, K,C>=0, thresholds T(k) can be fixed before A and n_k; a base
with upper limit at most c and lower limit at least c outside range(n_k),
where n_k>=T(k), has a superset witnessing the conjectured limit c.

The axiom audit `SparseRepairAxiomCheck.lean` passes. See
`SparseRepairProgress.md` for the statement and construction. There is
still no suitable base set, so Spec is unchanged and unresolved.

## Joint finite and infinite repair engine completed

Ten new files culminate in `Erdos66JointInfiniteRepair.prescribed_spikes`.
Under explicit uniform prefix costs (weighted collision reciprocals and
forbidden-choice masses) and a bounded prefix sum of 1/sqrt(q_i), it adds
prescribed even representation spikes to ANY O(log n)-bounded base set,
with total collateral o(log n). The entire packet collection has at most
two non-designated self-representations at each target. Uniform mixed-hit
potentials and compactness supply one infinite selection.

All ten files compile and have oleans. Three audits pass, including
`JointInfiniteRepairAxiomCheck.lean`. See `JointRepairProgress.md` for exact
hypotheses and pipeline. The geometric-target application is now proved, as
a special case of polynomially sparse completion below. No suitable base set
has been constructed, and Spec remains unchanged and unresolved.


## Polynomially sparse and dyadic exceptions can now be completed

Four files, ending with `PolynomialSparseCompletionExplore.lean`, prove:
if A has a global O(log n) envelope, asymptotic upper coefficient c>0, and
asymptotic lower coefficient c outside a strictly increasing sequence n_k
with n_k >= (k+1)^12 eventually, then some B containing A satisfies
r_B(n)/log n -> c. In particular, exceptions at all powers of two can be
repaired. The upper collateral from all repairs together is o(log n).

`PolynomialSparseCompletionAxiomCheck.lean` passes with permitted axioms only.
This is a conditional theorem, not a solution: no base meeting these
hypotheses is available. Independent random selection at fixed logarithmic
mean does not yield exceptions this sparse for shrinking relative errors.


## Matching-based strengthening completed

The old Sidon condition on all unintended packet sums has been replaced by
a matching-partition MGF estimate. For S=sum_i 1/sqrt(q_i), the restricted
MGF at each target is at most exp(4*S^2*(exp(8*t)-1)). This is independent
of coordinate index powers. Joint self/mixed potentials and compactness
produce o(log z) collateral under a single weighted summability condition.

`WeightedSparseCompletionExplore.lean` needs only
sum_k log(n_k+2)^(3/2)/sqrt(n_k+1)<infinity. The real-power comparison in
`SuperquadraticCostsExplore.lean` verifies it whenever n_k>=(k+1)^p
eventually for ANY fixed real p>2. The earlier exponent twelve is no longer
the best checked criterion. Injectivity suffices; monotonicity is not needed.

Both new audits pass. See `MatchingRepairProgress.md`. The original theorem
remains unresolved: independent random errors are still too dense as the
relative accuracy tends to zero, and no structured replacement base or
mixed-period transition has been constructed.


## Transition equations and a necessary repair budget checked

Four additional files, ending with `TransitionBudgetExplore.lean`, examine
whether sparse matching repairs can bridge a dense template transition.
For old A below N and new F at least N, all representation increments at
n<2N are exactly twice the mixed count. The first transition window is
therefore a Boolean linear-convolution feasibility problem, but no
feasibility theorem or control of the next quadratic window is supplied.

A uniform epsilon*log(N+2) increase on rho*N targets below 2N requires
at least epsilon*rho/(2K) times sqrt(N log(N+2)) added points if the old
set has at most K times that many points. More generally, negligible
added-point density gives negligible total normalized increment on any
finite target family. Thus sparse additions cannot fill a fixed positive-
proportion transition deficit. These are limitations on that approach,
not a disproof of the conjecture.

All four files compile and the axiom audit passes. See
`TransitionBudgetProgress.md`. No suitable base or valid mixed-period
transition has been constructed, and `Spec.lean` is still unchanged.
