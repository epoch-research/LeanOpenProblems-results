# Square-root fluctuation obstruction

## Status of the original task

`Submission/Spec.lean` is unchanged. The existential conjecture is still
neither proved nor disproved. In particular, none of the theorems below is a
valid replacement for its `sorry` or a theorem negating the conjecture.

## Newly checked results

1. `ConvolutionSquareStabilityExplore.lean` proves for real functions on a
   finite abelian group

       (sum f^2 - sum g^2)^2 <= sum_z ((f*f)(z)-(g*g)(z))^2.

   It uses reflection invariance of mixed convolution energy and the zero
   coefficient of a reflected convolution; no Fourier theorem is needed.

2. `WeightedPushEnergyExplore.lean` proves weighted infinite-sum
   Cauchy--Schwarz and the L2 bounds for residue periodization.

3. `WeightedSquareStabilityExplore.lean` proves, for nonnegative f and
   0<=r<1, under the stated summability hypotheses,

       max(0, sum f_n^2 (r^2)^n - sum g_n^2 r^n)^2
         <= sum ((f*f)_n-(g*g)_n)^2 r^n.

   The proof periodizes into ZMod m and sends m to infinity.

4. `FractionalFourthPowerExplore.lean` proves for the exact fractional
   harmonic profile p:

       (n+1) p_n^2 <= H_(n+1),
       Summable (p_n^4),
       F_(p^2)(r) * sqrt((1-r)/(-log(1-r))) --> 0.

   The first bound uses monotonicity and p*p=H. The second compares
   H_(n+1)^2/(n+1)^2 with 4/(n+1)^(3/2). The third follows from

       F_(p^2)(r)^2*(1-r) <= sum p_n^4.

5. `SquareRootFluctuationExplore.lean` applies the weighted inequality to
   f=1_A, g=sqrt(c)*p. The theorem

       Erdos66SquareRootFluctuation.squared_error_limit_lower_bound

   says that if c!=0, r_A(n)/log(n) --> c, and

       (r_A(n)-c H_(n+1))^2/log(n) --> d,

   then c/2 <= d. Its corollary

       Erdos66SquareRootFluctuation.not_squared_error_little_o_log

   excludes d=0.

## Verification

All five source files compile and have current oleans. Principal theorems
are audited in `WeightedStabilityAxiomCheck.lean`,
`FractionalFourthAxiomCheck.lean`, and `SquareRootFluctuationAxiomCheck.lean`.
Their only axioms are propext, Classical.choice, and Quot.sound.

## Why this does not settle the conjecture

The original hypothesis requires error o(log n), not o(sqrt(log n)).
Errors of order sqrt(log n), or larger but still o(log n), remain possible.
No convergence of squared error divided by log n follows from the original
hypothesis. The new obstruction therefore gives no universal contradiction.

The finite construction route also remains incomplete: flat families within
one finite field and carry averaging do not yet control transitions between
unrelated periods. No compatible family of infinite prefixes has been built.
