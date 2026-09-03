# Polynomial saving for each fixed-tolerance exceptional set

## Status of the original task

The conjecture is still unproved and undisproved. Spec.lean is unchanged and
retains its original sorry. No proof or disproof has been submitted.

## New positive endpoint

`Erdos66PowerExceptionalCounting.exists_power_saving_density_one_profile`
proves that for EVERY prescribed c>0 there are ONE set A and ONE exceptional
set E such that:

* sum_{n in E} 1/(n+2) is finite and E has natural density zero;
* r_A(n)/log n tends to c outside E;
* for EACH fixed epsilon>0, some alpha in (0,1) satisfies

      sum_{|r_A(n)/log n-c| >= epsilon} (n+2)^(-1+alpha) < infinity,

  and the number of these bad targets below N is o((N+2)^(1-alpha));
* the same A satisfies, for each fixed natural j, the eventual envelope

      |r_A(n)/log n-c| <= c/(j+1)+32(j+1).

The coefficient c and set A do NOT change with epsilon or j. Alpha is allowed
to depend on epsilon. No common positive power saving for the diagonal E is
asserted; its proved bound remains harmonic summability.

## Checked machinery

* `BernoulliCostSelectionExplore.lean` generalizes the earlier finite
  Bernoulli/compactness construction to arbitrary countably many nonnegative
  continuous costs with summable, cutoff-uniform expected bounds. Finite
  initial segments of each cost row are harmless for summability.
* `PowerExceptionalProfileExplore.lean` multiplies the old harmonic-weighted
  potential at relative tolerance delta by (n+2)^a, with

      a=delta^2 c/256.

  The resulting expected bound is 2/(n+2)^(1+a), still summable. All reciprocal
  integer tolerances are selected simultaneously. For a requested absolute
  epsilon the proof takes delta c<epsilon and alpha=min(a,1/2).
* `SummableScaleCountingExplore.lean` proves that summability of
  1_E(n)/b(n), for positive monotone b tending to infinity, implies
  count(E,N)/b(N)->0. Its power specialization yields the displayed count.
* `PowerExceptionalCountingExplore.lean` combines these estimates with the
  previous envelopes and the single-exception-set diagonalization.

All production files compile and have built oleans. The main declarations
are audited by `PowerExceptionalAxiomCheck.lean` and
`PowerExceptionalCountingAxiomCheck.lean`, using only propext,
Classical.choice, and Quot.sound.

## Why this still does not invoke the completion theorem

The saving supplied by the exponential argument depends on the tolerance
and shrinks when the tolerance shrinks. The available repair theorem needs
summability of actual deficits weighted by sqrt(log(n+2))/sqrt(n+1), and also
an all-target asymptotic upper bound with coefficient c. Neither requirement
has been proved here. A positive power saving for every FIXED tolerance is
not a uniform power saving through a sequence of shrinking tolerances.

No incomplete-root estimate or efficient dense-deficit correction was
established during the construction review. Those remain possible research
directions, not checked implications. The unrestricted pointwise limit
required in Spec.lean is still missing.
