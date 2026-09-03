# Generating-function reductions

## Status

The conjecture is still **not proved or disproved**. `Spec.lean` is unchanged
and still contains its original `sorry`. This file records auxiliary work only.

## Completed in `GeneratingExplore.lean`

Write F_A(r) = sum_{n>=0} 1_A(n) r^n for |r|<1.

1. `generating_identity` establishes the absolutely convergent Cauchy-product
   identity

       F_A(r)^2 = sum_{n>=0} r_A(n) r^n.

2. `harmonic_series` proves

       (1-r) sum_{n>=0} H_n r^n = -log(1-r).

3. `logarithmic_abelian_limit` proves a general Abelian transfer theorem:
   if f(n)/log n -> c and its power series converges inside the unit interval,
   then

       (1-r) sum f(n) r^n / (-log(1-r)) -> c,   r -> 1 from below.

   Proof: H_n/log n -> 1; for every eps>0 the coefficient error satisfies
   |f(n)-c H_n| <= eps H_n + D for some constant D. Summing and normalizing
   bounds the error by eps + D/(-log(1-r)).

4. `witness_generating_limit` applies this and positivity to give

       F_A(r) sqrt((1-r)/(-log(1-r))) -> sqrt(c).

   `witness_generating_limit_zero` gives the equivalent t=1-r statement.

5. `witness_generating_power_ratio` proves that for each integer k>=1,
   any hypothetical witness with c != 0 satisfies

       F_A(r^k)/F_A(r) -> 1/sqrt(k).

   This uses the finite geometric sum identity, the logarithm product formula,
   and the square-root normalization. No Tauberian theorem is assumed.

## What remains unresolved

The power ratios are compatible with the expected counting function

    A(N) ~ 2 sqrt(c/pi) sqrt(N log N).

An exact Tauberian transfer to that counting asymptotic has not been formalized.
More importantly, even that asymptotic would be only a necessary condition:
there is still no integer 0/1 construction giving r_A(n)/log n -> c != 0,
and no contradiction excluding all such constructions.

The finite-group results from earlier files do not supply such a construction;
integer carries, truncation, and cross-scale compatibility remain uncontrolled.

## Subsequent completion of the Tauberian step

The exact counting asymptotic has now been proved, without assuming Karamata,
in `TauberianProfileExplore.lean`. See `TauberianProgress.md` for the polynomial
moment, continuous-test, and cutoff proof pipeline. This remains only a
necessary condition and does not settle the conjecture.
