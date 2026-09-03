# Further gap investigations — no new settlement

Spec.lean is unchanged and unresolved. The completed formal reductions and
variance counterestimate are recorded in ProgressFourFactor.md and
ProgressVariance.md. No new prime-pair lower bound was obtained in this phase.

## Important distinction about the target

The conditional four-factor gap with a fixed positive δ would give a linear
prime correlation lower bound. The original conjecture asks only infinitude,
so this is stronger than necessary. A smaller positive correlation lower bound
could suffice if it dominates the prime-power contribution and the finite
contribution of any hypothesized finite set of prime pairs. No such smaller
gain has been established. Qualitative o(N) Type-I estimates alone are not
sufficient to exploit a specified sublinear gain without further rates.

## Routes reconsidered, without successful estimates

1. Nonnegative Selberg-majorant residuals. A genuine mean-2 majorant is at
   the parity boundary: the leading Bonferroni lower bound can be zero. A
   sufficient simultaneous positive residual mass on composites would help,
   but has not been proved. Merely exhibiting composites in each coordinate
   separately, or using the upper sieve, does not supply that mass.

2. Secondary gains at the parity boundary. Even a small positive residual
   product might be relevant if all other errors were quantitatively smaller.
   Simple square/product constructions do not automatically give nonzero
   Selberg residual weights, nor enough mass. No usable gain was proved.

3. Expanding the remaining Mangoldt factors with a Heath-Brown-type identity.
   This does not automatically remove the hard Type-II configurations. If one
   discards terms with only short unweighted factors, the resulting error is
   smooth-supported but can have large combinatorial weights; smooth-number
   density alone is not a valid bound for that weighted error.

4. A bilinear lattice operator with long unweighted factors may have more
   structure than the fully arbitrary four-factor kernel. However no suitable
   spectral or lower-bound theorem has been proved here. Mellin phases and
   discrete aliasing must be controlled; naive continuous smoothing does not
   justify a discrete prime-pair estimate.

5. Changing or linearly combining small cutoffs does not obviously avoid the
   variance obstruction: every remainder with positive cutoffs below W is
   zero at primes and is -log(pq) at distinct primes p,q>W. A combination
   whose coefficients sum to one retains those two clusters. This observation
   has not been used to assert any statement about the original conjecture.

The next useful step must be an actual new lower/cross-correlation estimate,
or a genuine irrational counterexample. More conditional reformulations or
variance barriers do not settle the conjecture. No incomplete submission has
been made, and no unproved assumption has been inserted into Spec.lean.

## Additional review after the four-factor/variance checkpoint

No new theorem settling the conjecture was found; Spec.lean remains unchanged.

- Revisited a finite-cell/exceptional-measure route. The precise existing
  criterion is in `FiniteCells.lean`: an irrational bad point in a rational
  interval yields a whole bad floor cell of width at least `1/N^2`. A measure
  upper bound strictly below this would certify a prime pair. The current
  almost-everywhere and local positive-measure results supply no such bound.
  Near integers there is already an explicit bad interval of width `1/N`.
  No high-moment estimate eliminating the remaining bad cells was obtained.
- Revisited a lattice-coordinate change using convergents of the slope.
  It transforms the thin strip into a region for two independent integer
  linear forms, but their coefficients grow with the approximant denominator.
  A fixed-coefficient prime linear-forms theorem, or an error measured against
  the surrounding large square rather than the strip's area, cannot simply
  be applied. No sufficient uniform large-coefficient estimate was obtained.
- Rechecked generic/topological and real-number construction ideas. A null,
  meagre exceptional set need not be empty; dense successful Liouville slopes
  do not classify every Liouville slope. No nested-interval construction
  avoiding every sufficiently large prime input was established.
- A bounded direct-IP HTTPS reference check, bypassing the earlier DNS
  failure, also timed out. No external status or theorem was verified.

These are failed or incomplete avenues, not assumptions for a final proof.

## Review of a weaker gain and multiplicative-frequency estimates

Still no settlement or new prime-pair lower bound.

- `prime_power_error_bound_sharp` already supplies the explicit envelope
  `(log 4 + 12) * (log(alpha*N)*sqrt N + log N*sqrt(alpha*N))`.
  Thus a Mangoldt-correlation lower bound exceeding this envelope by an
  unbounded amount would suffice: a finite prime-pair set has bounded total
  prime correlation. Merely exceeding zero, or proving an unspecified
  sublinear gain, does not suffice to remove prime powers.
- Revisited the four-factor sum through multiplicative frequencies. A claim
  of cancellation for arbitrary separable factor weights needs to handle
  multiplicative phases and arithmetic resonances. Elementary mean-value or
  Cauchy--Schwarz estimates do not give the needed strict lower gap. No
  theorem exploiting the actual Möbius/Mangoldt coefficients at the required
  strength was proved.
- Changing cutoffs or expanding into more factors does not by itself remove
  the hard terms: rough semiprime inputs have the exact remainder value
  `-log(p*q)`, and the unweighted convolution factor can equal one. It is not
  valid to assume that every surviving term has a long free factor.



## Smoothing review after the uniform Mellin coefficient estimates

No new prime-pair lower bound or counterexample was obtained. Spec.lean is
unchanged.

- In logarithmic ratio coordinates, the interval corresponding to an output
  integer q near alpha*p has width log((q+1)/q), which tends to zero on the
  order of 1/p. The established compact-frequency Mellin estimates do not
  justify a minorant resolving this shrinking interval.
- In additive difference coordinates, the target interval has fixed width.
  This avoids that particular bandwidth issue, but leaves a signed product
  of two prime Fourier sums. The existing single-prime estimates and direct
  Cauchy--Schwarz bounds do not supply the required lower bound for that
  product. The two coordinate formulations must not be conflated.
- No claimed estimate here eliminates the high-frequency contribution or
  upgrades almost-everywhere prime-pair infinitude to every irrational slope.

These observations are records of an unsuccessful approach, not new assumed
lemmas for the final conjecture.

## Selberg identity review — no settlement

Reconsidered the pointwise identity

    (mu * log^2)(n) = Lambda(n)*log(n) + (Lambda * Lambda)(n),

where log^2 denotes the pointwise square, not Dirichlet-convolution squaring.
The convolution Lambda*Lambda is nonnegative. This identity was considered
mathematically in this pass, not added as an unverified Lean declaration.

After weighting by Lambda(floor(alpha*n)), isolating the prime-pair term
SUBTRACTS the nonnegative convolution term. Its nonnegativity therefore does
not give the needed lower bound. A sufficiently sharp upper bound for the
prime/semiprime mixed correlation is still required. Also, the existing
small-divisor Type-I estimates cannot be extended without proof to the full
Mobius convolution in the first term.

The alternative genuine nonnegative majorant
Lambda(n) + (Lambda*Lambda)(n)/log(n) does not circumvent this issue: the
necessary mixed correlation estimates have not been established. No final
conjecture declaration was changed, and no incomplete proof was submitted.

## Sign-support test: actual positive mass is not negligible

Newly verified in RemainderPositiveScales.lean, with details in
ProgressPositiveMass.md:

At the actual growing cutoffs W and scales N used in the four-factor
reduction, eventually

    sum_{0<n<=N} max(R_WW(n),0) >= N/5376.

The proof counts injective triples of primes r,s,q with r,s<=W<rs, q>W;
R_WW(rsq)=log q exactly. Two separated power bands have fixed reciprocal
prime mass, and dyadic PNT supplies the long q factor uniformly.

Consequently, the recently proved small-prime-factor support of positive R
cannot justify throwing away all positive values as o(N) mass. This does
not rule out refined signed cross-correlation estimates, and supplies no
such estimate by itself. Spec.lean remains unchanged and unresolved.

## Mellin review after the positive-mass obstruction

No new prime-pair lower bound or irrational counterexample was obtained in
this review. The original conjecture remains unresolved.

For a dyadic product block, the Mellin transform of the remainder is a
product of two Dirichlet polynomials. On a frequency interval of length
comparable to N, the available mean-square estimates for these products,
combined by Cauchy--Schwarz and the 1/N scale of a ratio-strip kernel, leave
an O(N times powers of log N) absolute budget. This does not give the strict
signed lower gap. The fixed-compact-frequency coefficient theorem does not
apply uniformly to frequencies of order N.

Even a hypothetical qualitative relative sup bound for one factor should
not simply be inserted and called sufficient: replacing its L2 role by a
supremum can lose the square root of that factor's length. No rate adequate
to absorb that loss was proved in this review. No zero-free-region estimate
or high-frequency signed cancellation theorem was added as an assumption.

A search of the imported Mathlib and FormalConjecturesForMathlib sources
found no directly applicable simultaneous-primality theorem. This is not a
claim about the external literature status of the conjecture.

## Lower-supported Selberg test: a completed almost-prime lower result

The new route did give a genuine positive lower bound, not just another
obstruction. See ProgressLowerSieve.md and AuditLowerSieve.lean.

For every irrational alpha>1, there are infinitely many prime inputs p for
which floor(alpha*p) has at most 6291457 prime factors, with multiplicity.
More precisely, at arbitrarily large sixth scales u, outputs can be sifted
free of all primes <=roughRoot u, where k<=roughRoot u iff k^524288<=u,
with weighted prime-input count at least u^6/(8 root64 u).

This uses the exact local Selberg cost, an elementary interval bound for
mu^2/phi, and a lower-supported test (1-omega_Z)*nu_R. Its possible size R^4
on rough outputs and all distribution/prime-power errors are retained.

It does not establish prime output: the chosen R=Z^1024 and the required
modulus range R^2 Z lie well outside the verified row range if Z is raised
to the square-root primality threshold. The original Spec.lean is still
unchanged and unresolved.

## Scale-averaging review after the exponential-divisor smoothing work

Still no settlement. Spec.lean retains its original conjecture and sorry.

Reconsidered whether reciprocal weighting or averaging over cutoffs could
bridge the two established smoothing regimes. No sufficient uniform estimate
was obtained. For nonnegative terms, pointwise smoothing convergence gives
Fatou's inequality in the direction

    sum of limiting terms <= liminf of smoothed sums.

Thus even divergence of every fixed-parameter smoothed reciprocal sum would
not imply divergence of the limiting Mangoldt reciprocal sum. Mass may escape
to larger input indices as the smoothing parameter decreases. Finite-window
convergence is not a remedy when the window depends on that parameter.

The already established comparison-scale divergence concerns an upper error
budget, not the actual signed correlation error; averaging does not turn
that budget into a usable vanishing bound. No uniform-integrability theorem,
signed-tail cancellation estimate, or simultaneous-primality lower bound was
proved in this review.

A further bounded reference fetch failed with DNS resolution failure, so no
external literature status was independently verified. No proof submission
was made.

## Further exact-target review after the nonlinear Type-I checkpoint

No new sufficient estimate or irrational counterexample was obtained, and
Spec.lean remains unchanged with its original sorry.

- A fresh search of the imported number-theory sources found no theorem
  covering simultaneous primality of p and floor(alpha*p) for every
  irrational alpha. Both external reference requests failed with DNS errors;
  no independently verified claim about the literature status is made.
- Reconsidered replacing the fixed-cutoff positive Type-I majorant by a
  sharper Selberg majorant. A lower bound still requires the mixed and joint
  distribution estimates at the larger cutoff. The current small-power
  divisor rows cannot be used at that cutoff. Counting rough outputs at the
  established smaller cutoff does not certify prime outputs.
- Reconsidered changing to lattice coordinates supplied by convergents.
  The thin strip still has growing coefficients or a short transverse
  direction. A fixed-coefficient prime-linear-forms theorem on large boxes
  does not by itself furnish a relative error for this thin strip.
- Reconsidered high-frequency Mellin cancellation. A relative supremum
  saving for a short Mobius factor, combined with the available mean-square
  estimates for the other factors, still loses a square root of the short
  factor's length. No estimate absorbing that loss was established.

These are unsuccessful checks, not newly assumed lemmas. No proof or
counterexample was added to the final submission file, and no incomplete
proof was submitted for verification.

## Reciprocal floor/ceiling check

`ReciprocalPrimePairs.lean` now verifies, for alpha>1 irrational and n>0,

    floor(floor(alpha*n)/alpha) = n-1,
    ceil(floor(alpha*n)/alpha) = n.

Here both inner floors and the outer floor/ceiling are natural-valued, with
real division between them. If n is prime and n>3, the reciprocal floor is
therefore not prime. All three principal declarations compile and print
only propext, Classical.choice, and Quot.sound in their axiom audits.

This prevents treating reciprocal exchange as a symmetry of the original
floor-prime relation. It is NOT a counterexample to Erdos 972: the reciprocal
slope is below one, and the assertion only covers the selected forward
outputs. The ceiling identity also does not supply a new prime-pair lower
bound. Spec.lean is unchanged and the conjecture remains unresolved.

## Exact dilated-Mangoldt obstruction

`DilatedMangoldtObstruction.lean` now verifies the obstruction to using a
bounded-function dilated-correlation criterion directly with Lambda.
For distinct primes r,s and every n != 1,

    Lambda(r*n) * Lambda(s*n) = 0.

Consequently, for N >= 1, the full sum on 1 <= n <= N is exactly
log(r)*log(s), and its normalized mean tends to zero. Nevertheless,

    sum_{1 <= n <= N} mu(n)*Lambda(n) = -theta(N),

so its normalized mean tends to -1 by the previously proved PNT.
These exact facts prohibit the proposed unbounded extension of the
orthogonality criterion. The successful compilation audits all three
principal declarations with only propext, Classical.choice, and Quot.sound.

This is a diagnostic obstruction, NOT a proof or disproof of Erdos 972.
The original conjecture and its sole import in Spec.lean remain unchanged.
No sufficient signed correlation lower bound or irrational counterexample
was found in this continuation.

## Logarithmic dilation check

See ProgressLogDilatedObstruction.md. The previously established unbounded
Mangoldt obstruction persists after reciprocal weighting and logarithmic
normalization. Distinct-prime dilated correlations tend to zero, whereas
the logarithmic mu--Lambda correlation tends to minus one. The generic
unrestricted logarithmic dilation criterion is now explicitly refuted in
Lean. This does not exclude a prime-output-specific criterion with extra
hypotheses, and does not settle Erdos 972. Spec.lean is unchanged.

## Least-factor refinement of the prime-input smoothing comparison

See ProgressLeastFactorComparison.md. A new actual pointwise error bound
retains log(minFac(n)), and the one-prime upper sieve bounds its weighted
mean by O(N log log N) at selected irrational good scales. The resulting
mixed prime--smooth comparison works at the explicit layerParameter, with
arbitrarily small normalized error relative to the genuine prime-pair sum.
This is not a lower bound for that mixed sum. No fixed-t smooth--smooth
limit may be substituted for the still-unproved variable-parameter mixed
lower bound. The conjecture in Spec.lean remains unresolved and unchanged.

## Whole-file library cross-check

A fresh scan tested co-occurrence anywhere in each Mathlib and
FormalConjecturesForMathlib source file, rather than requiring primality,
irrationality, and floor terminology to occur on the same line. No applicable
simultaneous-primality theorem was found. The rational-approximation matches
use coprimality and do not assert prime numerators and denominators. A separate
`exact?` attempt on the precise conjecture failed to close the goal
(`CheckExactGoal.lean` is an intentionally failing scratch check).

No mathematical lower bound or counterexample resulted from these checks.
Spec.lean remains unchanged with its original sorry. The earlier submission
of that incomplete state failed verification, as expected; it was not a
settlement, and the missing proof has not been supplied.

## Binary Fourier review after the least-factor comparison

No new sufficient lower bound or irrational counterexample was found in this
continuation. Spec.lean remains unchanged and still contains its original sorry.

Reconsidered the binary prime exponential-sum formulation with the weaker goal
of exceeding the existing O_alpha(sqrt(N) log(N)) prime-power envelope, rather
than proving an asymptotic. The signed product of the two prime sums still needs
an estimate not provided by the established one-prime bounds. Passing to absolute
values does not supply a positive lower bound. No missing signed estimate was
assumed, and no claim about an impossibility of stronger methods is intended.

Also reconsidered whether a fixed-parameter smoothed mean could be used only to
obtain a sublinear gain. This still requires a justified joint choice of smoothing
parameter and cutoff; the already documented limit-exchange gap remains. No new
Lean lemma or completed proof resulted, and the incomplete final file was not
resubmitted.

## Positivity/majorant follow-up

The original conjecture remains unresolved and Spec.lean is unchanged.
No new sufficient bound or irrational counterexample resulted from this review.

For nonnegative source weights f,g with majorants a>=f,b>=g, the exact
pointwise identity is

    f*g = a*g + f*b - a*b + (a-f)*(b-g).

Consequently, in a normalized idealization with means of f,g equal to one,
means of a,b equal to M,L, and the three mixed main terms evaluated, the
baseline lower bound is M+L-M*L. A strictly positive contribution from
simultaneously composite residuals is not by itself sufficient when that
baseline is negative: the residual product must exceed M*L-M-L, including
all errors. The established fixed-cutoff positive Type-I majorants have
means tending to infinity; the existing one-coordinate rough-semiprime
and positive-remainder counts do not supply this required joint excess.
No joint-composite lower estimate was assumed in this review.

Another attempt to verify applicable external literature failed: ordinary
DNS resolution was unavailable, and an HTTPS connection to a public DNS
endpoint also timed out. No external settlement or new imported theorem
was identified. No incomplete proof was submitted.
