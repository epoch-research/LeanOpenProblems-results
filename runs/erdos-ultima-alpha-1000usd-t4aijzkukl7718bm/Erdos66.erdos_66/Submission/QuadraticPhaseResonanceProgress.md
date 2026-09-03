# Quadratic real-parameter candidates and rational-approximation resonances

## Original task status

The conjecture is still neither proved nor disproved. Spec.lean is unchanged
with its original sorry. No valid solution or exact-negation proof has been
submitted.

## Proposed route and scope

This continuation investigated membership defined using one fixed real
parameter, rather than independently replacing finite palettes. The hope was
that close rational approximations might preserve old membership while giving
arithmetic structure at later scales. The checked result instead identifies
a resonance in a specific quadratic shrinking-window implementation.

For alpha real and w:Nat->Real, define

    phaseSet(alpha,w) = {n : exists z:Integer, |alpha*n^2-z|<=w(n)}.

This is only a candidate class. No reduction of arbitrary possible witnesses
to this class is asserted. No counting asymptotic for these phase sets is
assumed or proved in this pipeline.

## Production files

* QuadraticPhaseResonanceExplore.lean
* QuadraticPhasePeaksExplore.lean
* LiouvilleQuadraticPhaseExplore.lean

All three compile, with current oleans and no placeholders or new axioms.

## Finite resonance

`Erdos66QuadraticPhaseResonance.finite_resonance`:

Suppose p>0, m^2<p, u is a unit modulo p, and a*u^2=1 modulo p. If

    |alpha-a/p| <= delta,   delta>=0,
    delta*p^2 + m^2/p <= w(n)                 for every n<=p,

then

    sumRep(phaseSet(alpha,w),p) >= m.

The modulus does NOT have to be prime. For k<m, set x_k=(u*k mod p). These
are distinct. The rational quadratic remainders of both x_k and p-x_k equal
k^2 modulo p. Their perturbed real phases are at distance at most

    delta*p^2 + k^2/p

from integers. Consequently both endpoints lie in the phase set and sum to
p. This is an injection into the actual natural-number representation
finset, not a cyclic-only count or a numerical approximation.

Supporting declarations:

* phase_mem_of_small_remainder
* square_remainder
* reflected_remainder

## Polynomial-sized peaks

Set

    resonanceSize(p) = floor(sqrt(sqrt(p))/4).

`Erdos66QuadraticPhasePeaks.cubic_approximation_peak` proves that for p>=16,

    |alpha-a/p| <= 1/p^3,
    a*u^2=1 mod p for a unit u,
    w(n) >= 1/sqrt(n+1) for every n,

imply r(p)>=resonanceSize(p).

The scalar estimates, including

    resonanceSize(p)/log p -> infinity,

are checked. Hence infinitely many such approximations imply arbitrarily
large normalized peaks and exclude EVERY finite real limit for this phase
set. This approximation hypothesis is explicit; it is not claimed for all
irrational alpha.

The window

    logWindow(n) = sqrt(1+log(n+1))/sqrt(n+1)

satisfies the required lower bound. It is on the intended logarithmic
square-root scale, but this alone is not a theorem about the actual density
or mean representations of the resulting set.

## Explicit transcendental parameter

`Erdos66LiouvilleQuadraticPhase` takes

    beta = liouvilleNumber(2) = sum_(j>=0) 2^(-j!),
    alpha = beta^2,
    q_k = 2^((k+2)!),
    p_k = q_k^2.

The parameter alpha is proved transcendental over the integers. The finite
partial sum of beta through k+2 equals b_k/q_k with b_k coprime to q_k.
The coprimality is checked using the last numerator term, which is one
modulo two; it is not assumed from an unreduced fraction.

For k>=6,

    |alpha-b_k^2/p_k| <= 1/p_k^3.

The inverse of b_k modulo p_k supplies the required square unit. The p_k
tend to infinity, and the actual set A=phaseSet(alpha,logWindow) satisfies

    r_A(p_k)/log p_k -> infinity.

Principal names:

* phaseParameter_transcendental
* partialSum_coprime
* explicit_approximations
* frequently_explicit_approximations
* explicit_denominator_peaks
* explicit_quadratic_phase_unbounded_peaks
* explicit_quadratic_phase_no_finite_limit

## Meaning and remaining gap

Very accurate rational stabilization can introduce large reflection peaks,
not merely preserve old bits. This rules out the displayed approximation
mechanism and explicit candidate. It does not exclude badly approximable
parameters, more complicated phases, all real-parameter constructions, or
arbitrary natural-number sets. No uniform shrinking-target estimate for a
successful parameter, and no other infinite witness, was found.

The earlier adaptive-resolution and global repair gaps also remain open.
Nothing in these results is the negation of the conjecture in Spec.lean.

## Verification

QuadraticPhaseAudit.lean audits all 29 lemma/theorem declarations in the three
production files. The saved QuadraticPhaseAudit.log lists only propext,
Classical.choice, and Quot.sound.

QuadraticPhaseChecks.lean, QuadraticPhaseLimitChecks.lean,
LiouvillePhaseChecks.lean, and LiouvillePhaseFinalChecks.lean are name-search
scratch files containing failed checks, not production dependencies.
