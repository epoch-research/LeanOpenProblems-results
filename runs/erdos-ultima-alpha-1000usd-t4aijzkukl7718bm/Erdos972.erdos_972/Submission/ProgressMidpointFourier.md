# Actual midpoint Fourier-band estimate — conjecture still unresolved

`Submission/Spec.lean` is unchanged and still contains the original `sorry`.
No prime-pair infinitude proof or irrational counterexample has been found.
No incomplete proof was submitted.

## Verified files

* ParityFloorPrefix.lean
* MidpointFourierBounds.lean
* FullRecenterCovarianceScales.lean
* MidpointFourierScales.lean
* FullRowFourFactorReduction.lean
* TwoBandFourierObstruction.lean

All compile. The printed principal axiom audits list only propext,
Classical.choice, and Quot.sound.

## 1. Moving frequencies, not just fixed integer modes

The preceding continuation controlled each fixed finite set of integer
frequencies in the exact finite Fourier expansion. Here J=g(N)+1 and

    midpointFrequency(J,j) = floor(J/2)+j,  j in Z.

For every J and j,

    |midpointFrequency(J,j)-J/2| <= |j|+1.

Thus fixed j gives a frequency proportional to the full modulus, near
normalized frequency 1/2. This is genuinely outside the earlier fixed-k
low-frequency result.

The current addition treats denominator TWO. It does not claim estimates
for neighborhoods of all rational fractions a/q. General residue-class
estimates were considered but not proved here.

## 2. Actual parity-twisted arithmetic prefix estimate

Let

    P(n) = +1 if 2 divides n, -1 otherwise,
    R(n) = meanCenteredTypeII(W,W,n),
    v>=W^2, v<=N, L>=1, log N<=L-1, |m(W)|<=1.

P is exactly the divisor polynomial with coefficients -1 at 1 and +2 at 2.
Its divisor mean is zero and coefficient mass is three. Also

    phase(n/2) = P(n).

Using the actual dual prime-input rows and joint divisor rows, assume
uniformly for all prefixes X<=N

    |inputDivisorRow(alpha,2,X)-psi(X)/2| <= Ep,

and joint divisor-count error Bd for input divisors <=v and output divisors
<=2. Then `centered_parity_prefix_bound` proves

    |sum_{n<=X} [R(n)-mean_N R] P(g(n))|
      <= 2Ep + 64*v*L^3*(Bd+1).

All mean corrections remain present. The ingredients are:

* the exact prime parity sum 2*inputDivisorRow(alpha,2,X)-psi(X);
* the existing logarithmic divisor-profile moment bounds, whose parity
  model is exactly zero;
* both Type-I profiles in the recentered decomposition;
* the isolated small-Mangoldt cutoff, with total at most 7v;
* the actual global input mean times the parity prefix sum.

A useful new pointwise bound is

    |meanCenteredTypeII(U,V,n)| <= 5vL^2

when UV<=v and the stated logarithmic hypotheses hold. The proof uses the
actual logTail, proving 0<=logTail(V,n)<=log n, rather than estimating it
by an uncontrolled logarithmic mean.

## 3. Finite normalized Fourier-term bound

If |k-J/2|<=H, the exact identity

    phase((k/J)g(n))
      = phase((k/J-1/2)g(n))*P(g(n))

allows summation by parts using the preceding PARITY-TWISTED prefixes.
The floor map is retained, and monotonicity bounds the slow phase variation.
Consequently the input transform is at most

    (1+2*pi*H)*[2Ep+64vL^3(Bd+1)].

The output transform is bounded using the actual arithmetic remainder:

    |DFT(outputLift R)(k)| <= 5vL^2*J.

Thus `midpoint_fourier_term_bound` proves

    |FourierTerm(k)/J|
      <= 5(1+2*pi*H)vL^2*[2Ep+64vL^3(Bd+1)].

No output prime weight or arithmetic coefficient is replaced by a plain
lattice-point count in this estimate.

## 4. Same actual two-sided good scales

`FullTwoSidedScale` retains both actual dual prime rows and joint divisor
rows. `exists_full_recenter_covariance_scale` supplies these together with
OutputPrimeScale and all four previously proved small covariance/recentering
errors. It uses ONE invocation of the two-sided scale theorem.

At the existing scales

    N=scaleCutoff(alpha,u), v=root64(u), W=growingCutoff(u),
    Ep=scaledRowError(dualScaleLoss(alpha),u,v), Bd=118*v*u^4,
    L=1+log(alpha*N),

the midpoint term budget is absorbed by the already proved eventual dual
covariance budget and joint covariance budget. All error thresholds are
selected before choosing u.

`eventually_midpoint_term_small` proves that for each fixed j and each
positive epsilon, every sufficiently large u satisfying FullTwoSidedScale
has

    |FourierTerm(midpointFrequency(J,j))/J| <= epsilon*N.

`eventually_midpoint_band_small` extends this to any FIXED finite set of
offsets j, handling possible collisions in ZMod J.

## 5. Simultaneous zero and midpoint bands

`twoBands(J,S,T)` is the union of

    image(S -> ZMod J),
    image(j in T -> midpointFrequency(J,j) mod J).

`eventually_two_bands_small` proves its contribution is o(N), for every
fixed pair of finite integer sets S,T, on all sufficiently large actual
FullTwoSidedScale scales. The proof bounds absolute sums of normalized
mode terms. It therefore does not assume that the two images are disjoint
and does not lose overlap or cancellation terms.

`finite_primeSet_forces_negative_two_band_complement` proves that a finite
prime-pair set forces, for every S,T, every epsilon>0, and every B, one
common scale u>B, W>B, with OutputPrimeScale and FullTwoSidedScale, at which

    |frequencyCovariance(twoBands(J,S,T)^complement)/N + 1| <= epsilon.

This combines the full-row recentering obstruction with the two-band
estimate at exactly the SAME scale. No independent existential good-scale
sets are intersected.

## Remaining gap

Only fixed-width bands around 0 and 1/2 have been controlled. The theorem
is not uniform for bands growing polynomially with J, and it does not
control the full complementary Fourier sum. Ordinary output parity is
also not a substitute for the multiplicative parity issue in prime
sieving.

The required strict lower gap above -N for the remaining signed
contribution is still unproved. No sufficient prime-pair lower bound or
irrational counterexample has been obtained; the universal conjecture is
not settled.
