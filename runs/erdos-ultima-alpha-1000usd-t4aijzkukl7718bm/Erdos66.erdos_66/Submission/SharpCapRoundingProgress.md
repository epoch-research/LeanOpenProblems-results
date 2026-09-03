# Fixed additive caps and bounded-discrepancy rounding

## Original task status

The conjecture in Spec.lean is still neither proved nor disproved. Its
statement, import, and original sorry are unchanged. No proof was submitted.

## New production files

* OneSidedMomentExplore.lean
* PrefixAbelComparisonExplore.lean
* SharpCapRoundingObstructionExplore.lean

## Main restricted-class obstruction

`Erdos66SharpCapRoundingObstruction.bounded_rounding_sharp_cap_no_finite_limit`:

Let p be the exact fractional harmonic profile, p*p(n)=H_(n+1). If A satisfies

    |sum_(i<=n) (1_A(i)-p_i)| <= D            for every n,
    r_A(n) <= H_(n+1)+K                      eventually,

for fixed D>=0 and real K, then r_A(n)/log n has NO finite real limit.

The coefficient cannot be changed to evade this conclusion: bounded prefix
discrepancy forces any finite coefficient to equal one, and one is excluded.
This is NOT an existence theorem for sets satisfying these two restrictions.

## General one-sided error theorem

For any hypothetical witness A,c, put e_n=r_A(n)-c H_(n+1). Under the additional
hypothesis

    [sum_(i<=n) e_i]/(n+1) -> 0,

the error is neither bounded above nor bounded below. The upper error exceeds
any fixed real K arbitrarily late. Main names:

* no_bounded_upper_error
* no_bounded_lower_error
* upper_error_frequently_large

The small signed-prefix-mean hypothesis is explicit. It is NOT derived for
all witnesses. Bounded-discrepancy harmonic roundings do satisfy it, by the
existing cumulative convolution identity and the new checked profile Cesaro
limit.

## Finite moment and Abel arguments

If e_i<=K, K>=0, and |e_i|<=delta H_i+D with delta,D>=0, then

    sum_(i<=n) e_i^2
      <= K(D+delta H_n)(n+1)
         +(K+D+delta H_n)|sum_(i<=n) e_i|.

Consequently, if e_n/log n->0 and its signed prefix mean tends to zero,

    sum_(i<=n) e_i^2 / [(n+1)log n] -> 0.

The independent prefix-to-Abel comparison proves that a nonnegative f with
this vanishing cumulative normalization, and summable geometric series, has

    [(1-r)/(-log(1-r))] sum_n f_n r^n -> 0.

Its key exact formula and inequality are

    (1-r) series(prefixSum f,r)=series(f,r),
    prefixSum f <= prefixSum g+D  =>  series(f,r)<=series(g,r)+D.

Apply these to e^2. The already checked universal Abel lower coefficient c>0
contradicts the zero limit. Replacing e by -e proves the lower-sided version.
No Gaussian moment amplification, moving-target stabilization, or unproved
pointwise rounding estimate is used.

## Meaning for the construction search

One cannot obtain the conjecture by retaining bounded discrepancy while
forcing a fixed additive upper error above the harmonic mean. A successful
bounded-discrepancy construction, if one exists, must allow unbounded errors
of both signs. Such errors can still be o(log n), so the original conjecture
is entirely compatible with these results.

This sharpens the earlier unformalized observation in the continuation notes.
It does NOT invalidate the completion criterion with an asymptotic upper
coefficient: that criterion allows unbounded sublogarithmic upper errors.
No suitable rounding rule, changing-palette chain, or global repair meeting
the original conjecture's requirements has been obtained.

## Verification

The three production sources compile with current oleans. SharpCapRoundingAudit.lean
checks all 21 declarations; its saved log uses only propext, Classical.choice,
and Quot.sound. The production sources contain no sorry or added axioms.
OneSidedMomentChecks.lean and ShiftLimitChecks.lean are name-search scratch files
with intentionally failed checks, not production dependencies.
