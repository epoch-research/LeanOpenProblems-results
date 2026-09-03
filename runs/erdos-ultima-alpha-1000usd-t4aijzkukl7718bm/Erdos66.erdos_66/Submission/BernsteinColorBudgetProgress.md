# Variance-sensitive finite color budgets

## Status

The conjecture in Spec.lean remains unresolved and unchanged. These are finite
selection and transfer results, not an infinite natural-number construction.
No proof or disproof has been submitted.

## Checked bound

For centered bounded kernels, the exponential-moment calculation now keeps
the actual second moment V rather than replacing it with the squared range
M^2. Matching fibers use independent color pairs. The Bernstein parameters

    R=2(sqrt(V ell)+M ell), t=ell/(sqrt(V ell)+M ell)

work for V>=0, M>0, ell>0, including V=0. They give tM<=1,
Vt^2-tR<=-ell, and R^2<=8(V ell+M^2 ell^2).

A variable-threshold selector handles different V and M for each request.
Writing ell=log(4mh+2), the resulting ordered color energy is at most

    E(h,m,V,M)=128h^2 V ell+128h M^2 ell^2+2h M^2.

There is no longer a requirement ell<=h. The additional range term pays for
large lists. This does not mean the estimate uniformly dominates all prior
bounds; the constants and range/variance regime still matter.

One admissible character translate is chosen before later finite coarse
kernel lists. A single later coloring handles both signed and unsigned
energies by doubling the request list. For every fine target,

    (rootCount-h^2 mu)^2 <= 6h[8mu^2 h^2+2E(h,2m,V,M)].

For h>0 and mu>0 the exact normalized root bound is

    error^2/(h^2 mu)^2 <= 48/h
      +1536 V ell/(h mu^2)
      +1536 M^2 ell^2/(h^2 mu^2)+24 M^2/(h^2 mu^2).

Here ell uses the doubled request count when signed and unsigned energies
are requested together. Nonnegative K<=M also gives
V<=M mu-mu^2<=M mu.

The actual disjoint origin-repaired palette, for h^2+4h+2<p, yields

    (r_A-h^2 mu)^2 <= 2[M(10h+8)]^2
      +12h[8mu^2 h^2+2E(h,2m,V,M)].

The coarse sets may overlap, but their kernel list is finite. These counts
are in a finite product group; no changing-scale integer embedding is
asserted.

## Production and audit

All six production files compile with current oleans:

* VarianceMatchingExponentialExplore.lean
* VariableThresholdSelectionExplore.lean
* BernsteinColorEnergyExplore.lean
* BernsteinRootBudgetExplore.lean
* BernsteinActualBudgetExplore.lean
* BernsteinBudgetParametersExplore.lean

BernsteinColorBudgetAudit.lean audits sixteen principal declarations. Its
saved log contains only propext, Classical.choice, and Quot.sound. The six
sources contain no sorry, admit, or new axiom.

## Remaining gap

This keeps variance information and removes the former list-size condition,
but not the logarithmic list cost itself. It does not create a coarse
logarithmic profile, supply changing-operator prefix compatibility, or
produce a Boolean rounding with pointwise sublogarithmic quadratic error.
The normalized formula is not an unconditional vanishing-error theorem.

## Subsequent universal Bernstein refinement

UniversalBernsteinColorProgress.md records a checked eighteen-declaration
refinement: a finite mask list gives one coloring for all later nonnegative
kernels, with a quadratic-times-logarithmic leading alphabet cost and an
explicit range term. Actual infinite mixed counts and the same ordinary
natural carry operator are included. The coarse profile and changing-scale
compatibility remain unresolved; this is not a solution of Spec.lean.
