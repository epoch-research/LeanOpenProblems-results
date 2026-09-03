# Verified sharp-count coefficient improvement

`GreedySharpSquareLower.eventual_power_lower` proves

    eventually M(N) >= N^(2/3)/1200.

Its dependencies are clean and its printed axiom audit lists only propext,
Classical.choice, and Quot.sound. This does not settle Erdős 773, does not
prove the exact epsilon=1/3 endpoint, and is not an exponent improvement.

## Parameters

Use `ControlledSquareSampling.logarithmic_sampling` with delta=1/1000:

    |A| >= (999/1000) N/log N,
    E(A) <= (83/1000) N^2/(log N)^3.

Let r=N^(1/4), p=1/r, mu=3(log N)^2/r,
D=(8/3)r/(log N)^2, and m=ceil(D^(1/24)).
The exact retained-edge inequality follows from 249/1000 < 999/4000.
The existing pair-codegree bound and overlap estimate are unchanged.

Tight rounding gives m^24(log N)^2 <= (208/75)r, so
r(log N)m^8 <= (10/7)(N log N)^(1/3).
Use the unchanged horizon tau=(log N)^(1/3)/100. The volume bound
N<=m^97 supplies its budget. Weaken the carrier density to 20/21 in the
last conversion; (42/5)(10/7)=12 yields the clean constant 1/1200.

## Files

- GreedySharpSquareScales.lean: scalar and degree estimates, exact conversion.
- GreedySharpSquareLower.lean: actual application to the square carrier.

The finite growing-horizon certificate was not changed, nor were any
concentration hypotheses added. The final submission Spec.lean is unchanged
and still has its unresolved admission for 0<epsilon<=1/3.
