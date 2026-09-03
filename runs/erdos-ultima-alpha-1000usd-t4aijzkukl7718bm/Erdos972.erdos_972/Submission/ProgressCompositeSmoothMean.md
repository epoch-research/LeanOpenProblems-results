# Composite-only fixed-parameter smooth mean — not a settlement

`Submission/Spec.lean` remains unchanged with its original `sorry`.
No sufficient prime-pair lower bound or irrational counterexample has been found.

## Verified file

`Submission/CompositeSmoothMean.lean`, namespace
`Erdos972CompositeSmoothMean`.

Let `S_t(n)` be the existing smooth Mangoldt function and `g(n)=floor(alpha*n)`.
The new sum retains only terms for which neither coordinate is prime:

    C(t,alpha,N) = sum_(0<n<=N)
      if n prime or g(n) prime then 0 else S_t(n) S_t(g(n)).

For `alpha>=1`, `t>0`, `removal_bounds` proves

    0 <= smoothCorrelation(t,alpha,N) - C(t,alpha,N)
      <= [pi(N)+pi(g(N))]/t^2.

It uses the already verified uniform bound `0<=S_t(n)<=1/t`, an elementary
union bound, and injectivity of the floor map. Unit inputs contribute zero.
The removed sum includes EVERY term with a prime in either coordinate,
not just the simultaneous-prime terms.

`output_prime_density_tendsto_zero` proves `pi(g(N))/N -> 0` using
`pi(M)/M -> 0`, `N<=g(N)<=alpha*N`, and positivity for positive N.
Consequently `removed_mean_tendsto_zero` shows that the displayed difference,
divided by N, tends to zero for each FIXED t>0.

Combining this with the existing all-cutoff smooth mean gives
`composite_smooth_mean`: for every irrational `alpha>=1`, every fixed t>0,

    C(t,alpha,N)/N -> [dampedMean(t)/t]^2.

Thus the entire fixed-parameter main term survives deletion of all prime
inputs and outputs. Its scalar limiting value as t->0+ is still one, but
this is an ITERATED limit. The factor `1/t^2` in the removal estimate is
retained, and no uniform assertion for moving t is made.

## Scope

This result confirms that the fixed-parameter positive mean alone does not
isolate prime pairs. It is not a counterexample to the conjecture and does
not rule out signed estimates in the finite window of the two-scale
minorant. No such sufficient estimate was obtained.

The file compiles. All three printed principal axiom audits list only
`propext`, `Classical.choice`, and `Quot.sound`. The file contains no `sorry`.
No original conjecture statement or import was changed, and no incomplete
proof was submitted.
