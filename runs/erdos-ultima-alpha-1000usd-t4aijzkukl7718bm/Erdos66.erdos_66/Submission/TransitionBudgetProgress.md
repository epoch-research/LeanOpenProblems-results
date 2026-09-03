# Exact transition equations and repair budgets

## Original task status

The original theorem in `Spec.lean` is still unproved and undisproved. Its
statement, import, and `sorry` are unchanged. No proof has been submitted.

The newest work examined whether matching-based sparse repair could bridge
the dense transitions left by the finite-template construction. It did not
supply a base set. Instead it checked the exact linear transition problem
and a necessary point budget for filling its deficits.

## Checked transition equation

Let A be a finite subset of [0,N), and let every point of F be at least N.
For every n<2N, two new points cannot sum to n, and therefore

    r_{A union F}(n) = r_A(n) + 2 r_{A,F}(n).

For N<=n<2N, every old a is at most n, so this is exactly

    r_{A union F}(n) = r_A(n) + 2 sum_{a in A} 1_F(n-a).

`Erdos66TransitionLinear.transition_constraints_iff` rewrites the finite
approximation constraints on this whole window as these Boolean linear
constraints. No feasibility theorem for them is proved. New/new sums
appear in the next window, so the equivalence does not eliminate the
future quadratic compatibility requirement.

All representation counts below N are unchanged by the extension.

## Checked total deficit budget

For disjoint finite A and F and any finite target family T,

    sum_{n in T} (r_{A union F}(n)-r_A(n)) <= 2 |A| |F| + |F|^2.

If the new set reaches a prescribed lower profile q(n) on T, then

    sum_{n in T} max(q(n)-r_A(n),0) <= 2 |A| |F| + |F|^2.

In particular, a uniform increase d on T requires

    |F| >= sqrt(|A|^2+d |T|)-|A|.

In the first transition window n<2N, the sharper budget is 2|A||F|,
with no |F|^2 term. Consequently, when

* |A| <= K sqrt(N log(N+2)), K>0;
* |T| >= rho N, rho>0;
* every n in T is below 2N;
* each target receives at least epsilon log(N+2) new representations;

one necessarily has

    |F| >= epsilon*rho/(2K) * sqrt(N log(N+2)).

The theorem `dense_transition_not_negligible` packages this as a failure of
vanishing normalized added-point cardinality along any such family of
transitions. Its negation concerns this particular procedure, NOT the
existential conjecture in `Spec.lean`.

More generally, if |A_k|=O(R_k) and |F_k|/R_k -> 0 for eventually positive
R_k, then the total representation increment on ANY finite target families
T_k, divided by R_k^2, tends to zero.

## Files and audits

* `NatPairAlgebraExplore.lean`: finite natural-number mixed-pair algebra,
  union identities, and total pair mass.
* `TransitionLinearExplore.lean`: exact first-window formulas, preservation
  below the cutoff, and the linear-constraint equivalence.
* `AdditiveDeficitMassExplore.lean`: general increment/positive-deficit mass
  bounds and an explicit cardinality lower bound.
* `TransitionBudgetExplore.lean`: the dense transition bound, its
  non-negligibility corollary, and normalized increment convergence.

All four compile and have built oleans. `TransitionBudgetAxiomCheck.lean`
reports only propext, Classical.choice, and Quot.sound for all main results.

## Remaining mathematical gap

The finite templates still have no proved compatible change-of-period
construction. The matching-based theorem repairs genuinely sparse
exceptions, but a positive-proportion transition deficit needs new points
on the same sqrt(N log N) scale as the old set. Their mixed counts must be
constructed, not treated as negligible collateral. No valid method for
this has been obtained, and no contradiction for all possible witnesses
has been proved.

## Subsequent extension test

See `PrefixLookaheadProgress.md`. Arbitrarily long accurate finite annular
histories can already force a large peak in the NEXT target window, using
only points inside the chosen prefix. Such prefixes admit no monotone
extension retaining the prescribed next-window upper bound. This excludes
an arbitrary-history extension rule, not carefully selected prefixes and
not the original conjecture.
