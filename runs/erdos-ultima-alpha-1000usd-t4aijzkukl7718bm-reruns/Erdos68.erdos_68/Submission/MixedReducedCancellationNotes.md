# Reduced cancellation can defeat the termwise lower bound

This is auxiliary progress, not a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

## Lean-verified finite example

Define

    R = sum_(k=2)^5 1/(k!-1)
        + 1/6! + 1/(6!)^2
        + sum_(k=7)^10 1/k!.

`MixedReducedCancellation.lean` verifies

    R = 7057699/5630400,
    0 < 5630400*(alpha-R) < 1.

The displayed fraction is reduced. The proof uses the existing positive
mixed-truncation error bound for the lower inequality and the partial sum
through 11!-1 with its established tail bound for the upper inequality.
No numerical oracle is used. All printed axiom checks contain only
`propext`, `Classical.choice`, and `Quot.sound`.

In the notation of `GeometricClearingBarrier.lean`, this is

    mixedApprox 2 4 (fun k => if k=0 then 2 else 1).

Thus it has four exact original rows, followed by five geometric prefixes.
It lies within the index range of that file's termwise-clearing theorem.
But its reduced denominator is divisible by neither 5!-1=119 nor (6!)^2.
The prime 7 from 119 has canceled. The reduced denominator factors as

    5630400 = 2^6 * 3^2 * 5^2 * 17 * 23.

The theorem `reduced_denominator_does_not_obey_termwise_barrier` explicitly
refutes the corresponding greater-than-one inequality with the reduced
denominator in place of a termwise-clearing multiplier.

This is not a contradiction to the previous theorem: its divisibility
hypotheses are genuinely necessary. Nor is one small positive scaled error
an irrationality proof. A suitable infinite family is still missing.

## External exact search that located the example

For an exact prefix through K, and geometric rows K+1 through N, the search
used

    r_k in {max(1,floor(depth/log(k!))),
            max(1,floor(depth/log(k!)))+1}.

Parameter ranges:

    K in {1,2,3,4,5,7},
    N in {8,10,12,14},
    depth in {12,24,48,96}.

There were 85,000 exact rational approximants. All reduced scaled errors
were enclosed using the exact partial sum through 100!-1 and the positive
upper tail 2/(101!-1). For each of the 96 parameter groups, the script saved
the choice minimizing the upper endpoint of that enclosure. Three saved
choices had upper endpoint below 1; all other saved choices had lower
endpoint above 1. No saved choice was ambiguous.

Artifacts:

* `/tmp/nonrectangular_factorial_search.py`
* `/tmp/nonrectangular_factorial_search.json`
* `/tmp/nonrectangular_factorial_search.log`

The search is not a Lean proof; only the finite example above was formalized.

## A natural family did not supply an asymptotic argument

The example at K=5 belongs to

    R_K = S_K + sum_(j=K+1)^(2K) 1/j! + 1/((K+1)!)^2.

The 38 cases 3<=K<=40 were separately checked with exact rational arithmetic
and the same enclosure of alpha. Only K=3 and K=5 have scaled errors below
1; the other 36 lie above 1. Selected diagnostics:

    K | reduced denominator bits | log10 scaled error
    3 |                        9 |         -0.922262
    5 |                       23 |         -0.404401
   10 |                      134 |         22.795648
   20 |                      622 |        145.131352
   40 |                     3000 |        800.564865

The logarithms are floating-point diagnostics; the interval classifications
are exact. Artifacts:

* `/tmp/mixed_one_square_family.py`
* `/tmp/mixed_one_square_family.json`

These finite checks do not establish asymptotic impossibility and do not
settle the conjecture. No proof has been submitted.
