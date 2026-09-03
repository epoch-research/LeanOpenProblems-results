# Fixed row removal does not yield linear Lambert tails (verified)

This is an auxiliary obstruction, not a solution of Erdős 68. The original
conjecture in `Submission/Spec.lean` remains unchanged and unproved.

`Submission/ShiftedLambertTailBarrier.lean` defines

    A_m^(K) = sum_(d|m, d>=2, d>=K) m!/(d!)^(m/d),

which retains only the Lambert rows indexed by d>=K. It verifies summability
of sum A_m^(K)/m! by comparison with the original Lambert series.

The main theorem `shifted_lambert_tail_exceeds_linear` proves

    for every K,C,N there exists n>=N with
    C*n < n! [sum_(m>=0) A_m^(K)/m! - sum_(m=0)^n A_m^(K)/m!].

Thus removing a fixed finite set of initial geometric rows never produces
the linear tail bound required by the new congruence-and-primes criterion.

## Proof

Set d=max(K,2). The retained d-row contributes 1/(d!)^k at index d*k.
At n=d*k-1, the scaled tail is therefore at least n!/(d!)^k. For large k,

    C*(d!)^k < k! <= (d*k-2)!.

The first inequality follows from factorial growth dominating every fixed
exponential, by using the base (C+1)*d!. Multiplying by n gives the strict
lower bound C*n < n!/(d!)^k. These choices of n can exceed any prescribed
cutoff N.

The printed axiom audit lists only `propext`, `Classical.choice`, and
`Quot.sound`. This strengthens the earlier obstruction, which treated only
the original coefficient sequence and the particular bound n-1.

No new descent of the reduced rational tails or compatible small-tail
representation has been obtained. No proof or disproof has been submitted.

## Retained congruences, also verified

The file additionally proves

* `lambertCoeffFrom_prime`: A_p^(K)=1 for prime p>=K;
* `lambertCoeffFrom_modEq_pred`: A_m^(K)=1 modulo m-1 when m>=max(K,2).

Thus the arithmetic properties survive this particular modification; the
linear tail bound is precisely the hypothesis that still fails. These facts
do not transfer to arbitrary carry-normalized coefficients.
