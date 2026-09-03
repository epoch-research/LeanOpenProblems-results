# Mixed smooth and two-scale fixed means — not a settlement

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No sufficient moving-parameter lower bound or irrational counterexample has
been found. No proof was submitted as a settlement.

## MixedSmoothMean.lean

For every irrational alpha>=1 and every FIXED s,t>0, the file proves the
all-cutoff limits

    sum_(0<n<=N) E_s(n) E_t(floor(alpha*n)) / N -> m(s)m(t),
    sum_(0<n<=N) S_s(n) S_t(floor(alpha*n)) / N -> [m(s)/s][m(t)/t].

Here E is expDivisorSum, S is smoothMangoldt, and m is dampedMean.
The proof uses a common sufficiently large divisor cutoff for both fixed
parameters, the existing uniform mean-square tails, and the existing
all-cutoff joint divisor-row means. The n=1 correction is retained and
bounded in absolute value by one before division by s*t.

For the ACTUAL two-scale expression previously defined in
TwoScalePairMinorant.lean, write a(t)=m(t)/t and

    pairMean(t) = (32/63) [7 a(t)^2 - 6 a(t)a(2t)].

`pairMinorant_fixed_mean` proves

    pairMinorantSum(t,alpha,N)/N -> pairMean(t)

for each fixed t>0. `pairMean_tendsto` proves the OUTER limit
pairMean(t)->32/63 as t->0+. Thus the formerly formal scalar benchmark is
now a proved ITERATED mean result.

`eventually_fixed_linear_pairMinorant` proves, for each irrational alpha>=1,
that for all sufficiently small positive FIXED t, eventually all N satisfy

    N/4 < pairMinorantSum(t,alpha,N).

The cutoff threshold may depend on t and alpha. This does NOT assert that
any of those N satisfy t*log(floor(alpha*N))<=1/4, which is needed to apply
the finite pointwise minorant for the Mangoldt product.

## CompositePairMinorantMean.lean

A general signed removal lemma proves that, for a fixed sequence a(n) with
|a(n)|<=C and fixed C>=0, deleting every term with a prime input OR a prime
output changes its normalized sum by a quantity tending to zero. The finite
absolute difference is bounded by

    C [pi(N)+pi(floor(alpha*N))].

The file also proves the bound

    |pairMinorant(t,m,n)| <= 16/t^2,    t>0.

Consequently `composite_pair_fixed_mean` proves the SAME fixed-parameter
mean pairMean(t) after deleting all prime-coordinate terms from the signed
two-scale sum. Neither remaining coordinate is prime. This is not a claim
that either coordinate lacks proper prime-power values.

Thus the positive fixed-parameter two-scale mean does not itself detect
prime pairs. In particular its convergence thresholds cannot be inserted
into the shrinking finite validity window without another estimate.

## Verification and remaining task

Both files compile. The printed principal axiom audits list only propext,
Classical.choice, and Quot.sound. Neither file contains a sorry.

No arithmetic lower bound in the required moving-parameter window was
proved. No statement or import in the original Spec.lean was changed.

## Later finite-window comparison

`ProgressCompositePairWindow.md` records an actual upper bound by the
proper-prime-power budget for the composite-only sum in the admissible
window. It yields an actual normalized error bounded away from zero
relative to the fixed-t mean for every admissible moving parameter sequence.
This strengthens the limit-order warning for the DELETED sum; the full
moving-parameter lower bound required by the conjecture remains unproved.
