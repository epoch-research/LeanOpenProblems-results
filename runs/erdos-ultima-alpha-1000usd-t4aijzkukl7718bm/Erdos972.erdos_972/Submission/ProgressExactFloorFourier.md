# Exact floor Fourier expansion and genuine low-frequency estimates

The conjecture remains UNSOLVED. `Submission/Spec.lean` is unchanged and
still contains the original `sorry`. No irrational counterexample or
sufficient full-correlation lower bound has been obtained. No incomplete
proof was submitted.

## New verified files

* FloorCovarianceFourier.lean
* FloorStripRatioDependence.lean
* RecenteredRemainderPrefix.lean
* RecenteredPrefixScales.lean
* FiniteFloorFourierBounds.lean
* LowFloorFourierScales.lean
* HighFloorFourierObstruction.lean

All compile, and the principal axiom audits list only propext,
Classical.choice, and Quot.sound.

## 1. Exact finite Fourier representation

For alpha>=1 let g(n)=floor(alpha*n), M=g(N), J=M+1, and

    A_f(k) = sum_{1<=n<=N} [f(n)-mean_N(f)] e(k*g(n)/J),
    B_g(k) = DFT(j -> g(j.val))(k),  k in ZMod J.

`floor_covariance_fourier` proves exactly

    Cov_N(f,g o floorMul) = (1/J) sum_k A_f(k)*B_g(k).

This is an equality in C after casting the real covariance. There is no
wraparound error because J is larger than every sampled output. The
floor phase is retained; it is not replaced by alpha*n. The input mean
is retained explicitly, so the zero mode is exactly zero.

`frequencyCovariance` is the real contribution from a finite frequency
set. `floor_covariance_frequency_split` gives an exact decomposition into
ANY such set and its complement. `recentered_fourFactor_frequency_split`
specializes this to the actual meanCenteredTypeII remainders.

## 2. Why a ratio-only Mellin kernel is not automatic

`no_ratio_only_floor_kernel` proves, for alpha>1 irrational, that no
function K of q/n alone can equal 1_{q=floor(alpha*n)} for all positive
integers n,q. A dilation preserves q/n but can leave the additive
unit-width strip. This does not rule out a scale-dependent,
higher-dimensional, or suitably smoothed Mellin representation.

The finite Fourier formula above is NOT identified with the previously
bounded lowMellinFourFactor integral.

## 3. New arithmetic prefix estimate

For U,V>0 define

    C(U,V) = divisorMean(UV,constantCoeff(U,V))
             -m(U)*divisorMean(V,constantCoeff(1,V)).

The exact recentered Type-I profile is

    profile(U,V) - m(U)*profile(1,V) + Lambda_{<=V}.

The logarithmic slopes cancel EXACTLY. Under UV<=v<=N, |m(U)|<=1,
L>=1, and log N<=L-1, uniformly for every X<=N,

    |sum_{n<=X} meanCenteredTypeI(U,V,n) - C(U,V)*X|
      <= 15*v*L^2,

    |sum_{n<=X} meanCenteredTypeII(U,V,n)
           - [psi(X)-C(U,V)*X]|
      <= 15*v*L^2.

After empirical centering,

    |sum_{n<=X} R(n) - (X/N) sum_{n<=N} R(n)|
      <= |psi(X)-(X/N)psi(N)| + 30*v*L^2.

This does not assume C(U,V) converges or is uniformly bounded, and uses no
quantitative Mertens rate. The one-coordinate divisor count has its exact
floor error bounded by one; no independent good scale is selected.

## 4. Uniformity on all sufficiently large common-cutoff scales

Let N=scaleCutoff(alpha,u), M=floor(alpha*N), W=growingCutoff(u),
R(n)=meanCenteredTypeII(W,W,n).

`eventually_recentered_prefix_model` proves for every epsilon>0,
on ALL sufficiently large u, simultaneously for all X<=M,

    |sum_{n<=X} R(n) - [1-C(W,W)]*X| <= epsilon*N.

It uses uniform prefix PNT and the existing vanishing polynomial/log
budgets, with m(W)<=1 eventually. No prime-output row hypothesis is
required for this one-coordinate statement.

`eventually_centered_remainder_prefix` proves the analogous empirical
centering bound, simultaneously for all enclosing intervals N<=Q<=M
and every X<=Q.

## 5. Actual fixed-frequency smallness

Finite summation by parts retains the floor phase and uses its monotone
variation. If a centered input prefix error is E, then at integer k,

    |A_f(k)| <= [1+2*pi*|k|]*E.

If output prefixes have model rho*X with error E, f(0)=0, |rho|<=E,
and k is nonzero modulo J, then

    |DFT(outputLift f)(k)| <= [2+2*pi*|k|]*E.

The constant model's contribution is -rho, not discarded: the sum of
the nonzero-index characters is -1. For the actual remainder, R(1)=0
and the X=1 prefix estimate supplies |rho|<=E.

`eventually_fourier_term_small` consequently proves that every fixed
integer k contributes o(N) AFTER the 1/J Fourier normalization.

`eventually_low_frequency_covariance_small` proves, for each FIXED
finite S subset Z, on all sufficiently large u,

    |frequencyCovariance(alpha,N,R,R,image(S -> ZMod J))| <= epsilon*N.

Possible collisions of the image are handled by a nonnegative finite-sum
bound. Neither injectivity nor a restriction on the modulus is assumed.

IMPORTANT: this theorem concerns each FIXED finite S. It is NOT a bound
uniform for frequency sets growing polynomially with N, nor for a fixed
positive fraction of all J modes.

## 6. Exact complementary-frequency obstruction

`finite_primeSet_forces_negative_high_frequencies` combines the above
with the already proved recentered finiteness obstruction. If the prime
pair set is finite, then for EVERY fixed finite S subset Z, every positive
epsilon and every B, there is one actual common good scale u>B, W>B,
with OutputPrimeScale(alpha,u), at which

    |frequencyCovariance(alpha,N,R,R,image(S)^complement)/N + 1|
      <= epsilon.

All eventual thresholds are chosen before selecting the common scale.
There is no intersection of independent existential good-scale sets.

## Remaining gap

The exact full Fourier representation and a genuine fixed-low-frequency
estimate are now available. The negative contribution required by a
counterexample would have to escape every fixed finite frequency set.
No sufficient signed estimate on that complementary contribution has
been proved. A strict lower gap above -N, a different prime-pair lower
bound, or an actual irrational counterexample is still needed.
