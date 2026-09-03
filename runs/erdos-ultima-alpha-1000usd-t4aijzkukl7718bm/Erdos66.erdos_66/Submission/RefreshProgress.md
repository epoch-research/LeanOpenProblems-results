# Partial refresh: exact drift, variance-sensitive noise, and its tail-budget tradeoff

## Original task status

The conjecture in Submission/Spec.lean remains unproved and undisproved.
Its import, statement, and original sorry are unchanged. No proof has been
submitted. These are auxiliary finite results, not a solution.

## Verified production results

The following eight files compile and have current oleans:

* BernoulliVarianceExplore.lean
* RefreshAlgebraExplore.lean
* RepVarianceExplore.lean
* RefreshVarianceExplore.lean
* HarmonicRefreshExplore.lean
* RefreshBudgetExplore.lean
* BalancedRepVarianceExplore.lean
* BalancedHarmonicRefreshExplore.lean

RefreshAudit.lean audits 34 declarations. Its saved log contains only
propext, Classical.choice, and Quot.sound.

### Exact refresh drift

For a Boolean old sequence a, a profile p in [0,1], and 0<=theta<=1, define

    q_i=(1-theta)a_i+theta p_i.

The exact finite representation mean is

    (1-theta)^2 r_A + 2theta(1-theta)(a*p) + theta^2(p*p) + diagonal.

The diagonal lies in [0,theta]. For the checked harmonic fractional profile
p and e=a-p, at every n within the cutoff:

    mean=H_(n+1)+2(1-theta)(e*p)(n)+(1-theta)^2(e*e)(n)+diagonal.

If all prefix discrepancies of e have absolute value at most D, then

    |mean-[(1-theta)^2 r_A+theta(2-theta)H_(n+1)]|
      <=4theta(1-theta)D+theta.

Thus a small refresh contracts the old quadratic defect only slightly.

### Variance-sensitive MGF

For disjoint Bernoulli monomials with probabilities u_k and weights
0<=w_k<=2, the centered MGF satisfies

    E exp(t(F-E F)) <= exp(2t^2 V),     |t|<=1/2,
    V=sum w_k u_k(1-u_k).

Unlike the old mean-scale proxy, V vanishes on deterministic monomials.
The finite summed-tail selection theorem now accepts this separate proxy.
For natural representations, unordered off-diagonal pairs have weight two
and the diagonal singleton has weight one. All independence needed is
within one target; targets are not assumed independent.

For the partial refresh:

    V <= theta[(2-theta)r_A+2(1-theta)(a*p)+theta(p*p)+1].

For the harmonic profile with bounded prefix discrepancy this yields

    V <= theta[(2-theta)(r_A+H)+4(1-theta)D+1].

### Actual finite selection

`exists_harmonic_refresh` produces a finite B, supported through L, with

    |r_B(n)-H_(n+1)|
      < (1-theta)^2 |r_A(n)-H_(n+1)|
          +4theta(1-theta)D+theta+epsilon V(n)

on a finite target set, PROVIDED V dominates the displayed proxy and

    sum_targets 2 exp(-epsilon^2 V(n)/8) < 1.

This version does not assert preservation of prefix discrepancy in B.

### Prefix-balanced dependent version (also completed)

`exists_prefix_balanced_variance_bound` combines the new variance MGF with
the prior compensated dependent-rounding theorem. The output retains all
prefix floor/ceiling brackets of its input probabilities, with

    |r_B(n)-mean(n)|<epsilon V(n)+2.

The additive two exactly pays for the prior exp(2|t|) compensation; it does
not grow with the number of coordinates or the number of target tests.

`exists_balanced_harmonic_refresh` specializes this to the refresh of a
bounded-discrepancy harmonic-profile rounding. The same finite B satisfies

    prefix discrepancy through L+1 <=1+(1-theta)D,

and the earlier representation bound with only an additional +2.
This removes the finite prefix-invariant loss; it does NOT remove the tail
budget. The finite B is not claimed to have global bounded discrepancy past
its support. No fixed-bit prefix-preservation or convergent infinite chain
is asserted by this theorem.

### Exact limitation of this tail certificate

On the FULL dyadic window [N,2N), N>0,

    sum 2 exp(-alpha log(n)/8)<1  implies  alpha>8.

For V(n)=theta*b*log(n), if the certified noise coefficient

    epsilon*theta*b

is less than the contraction gain theta(2-theta)delta, then

    theta*delta^2>2b.

In particular, for fixed b>0 and theta<=1, this numerical certificate cannot
contract arbitrarily small error coefficients delta merely by choosing a
smaller refresh fraction or moving the window further out.

This is NOT a lower bound on all actual realizations, all independent
selection proofs, or all dependent repair algorithms. The noise bounds are
upper bounds and the union-budget criterion is sufficient. Failure of that
criterion does not imply nonexistence. Nothing here disproves the conjecture.
