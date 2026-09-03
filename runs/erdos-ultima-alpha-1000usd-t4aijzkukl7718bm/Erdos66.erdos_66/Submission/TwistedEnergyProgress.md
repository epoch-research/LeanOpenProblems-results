# Alternating convolution and parity splitting

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original sorry. No submission tool has been called for these
auxiliary results, which are not a solution.

## Verified files

* TwistedEnergyExplore.lean
* NaturalTwistedEnergyExplore.lean
* WitnessTwistedEnergyExplore.lean
* ParityRepresentationExplore.lean

All four compile and have current oleans. TwistedEnergyAudit.log audits
sixteen declarations, using only propext, Classical.choice, and Quot.sound.
TwistChecks.lean and ParityChecks.lean are scratch name-check files with
intentional failed checks, not production dependencies.

## Finite signed-energy comparison

For any real sign character chi on a finite abelian group, chi(x+y)=chi(x)chi(y)
and chi(x)^2=1, and arbitrary real f,g:

    corr(chi*f)(h) = chi(h) corr(f)(h),
    energy(f,chi*f) = sum_h chi(h) corr(f)(h)^2.

Cauchy--Schwarz and the preceding autocorrelation stability theorem yield

    [energy(f,chi*f)-energy(g,chi*g)]^2
      <= [sum_n (conv(f,f)(n)-conv(g,g)(n))^2]
           * [2 energy(f,f)+2 energy(g,g)].

This controls an ENERGY DIFFERENCE, not individual twisted coefficients.

## Natural transfer

Define

    alt(f)(n) = (-1)^n f(n),
    twistConv(f)(n) = sum_(a+b=n) f(a) (-1)^b f(b).

The cyclic sign character (-1)^(z.val) is well defined for even periods.
Weighted pushforward commutes with this character. For a summable sequence,
its residue pushforward at any fixed natural index tends to the sequence
value as the period tends to infinity; dominated convergence proves this.

Using periods 2(k+1), the finite comparison, weighted periodization bounds,
and finite natural partial sums gives

    sum_n [twistConv(f)(n) r^n]^2
      <= sum_n twistConv(g)(n)^2 r^n
           + sqrt(E * [2 F + 2 G]),

where

    E = sum_n [sumConv(f,f)(n)-sumConv(g,g)(n)]^2 r^n,
    F = sum_n sumConv(f,f)(n)^2 r^n,
    G = sum_n sumConv(g,g)(n)^2 r^n.

Assumptions explicitly include 0<=r<1 and summability of the weighted inputs
and displayed right-hand series. The theorem also proves summability of
the left-hand squared sequence. Note the r^(2n) weighting on the LEFT,
as opposed to r^n on the right.

## Specialization to the fractional harmonic model

The nonnegative antitone fractional profile p satisfies

    |sum_(j<N) (-1)^j p_j| <= p_0 = 1.

This follows by truncating the profile and applying Mathlib's alternating
series error bound. The earlier mixed-convolution bound then gives

    |twistConv(p)(n)| <= 2.

With g=sqrt(c)*p, c>=0, let

    E(A,c,r) = series(errorSq A c,r),
    H2(r) = series((harmonic(n+1))^2,r),
    T(A,r) = sum_n [twistConv(1_A)(n) r^n]^2.

For EVERY set A and 0<r<1:

    T(A,r) <= 4c^2/(1-r) + sqrt(E(A,c,r) * [4E(A,c,r)+6c^2 H2(r)]).

If r_A(n)/log n tends to any finite c, previous results give
E(A,c,r)*(1-r)/[-log(1-r)]^2 -> 0 and a uniform bound for the similarly
normalized H2. Therefore:

    T(A,r)*(1-r)/[-log(1-r)]^2 -> 0.

Main theorem:
Erdos66WitnessTwistedEnergy.witness_normalized_twist_zero.

## Exact parity identities and consequences

Set B={n:2n in A}, C={n:2n+1 in A}. The natural carry is retained:

    r_A(2(n+1)) = r_B(n+1)+r_C(n),
    r_A(2n+1)   = 2 sumConv(1_B,1_C)(n),
    twistConv(1_A)(2(n+1)) = r_B(n+1)-r_C(n),
    twistConv(f)(2n+1)=0 for every real sequence f.

Consequently every hypothetical witness has the POINTWISE mixed limit

    sumConv(1_B,1_C)(n)/log n -> c/2,

and the POINTWISE combined self-count limit

    [r_B(n+1)+r_C(n)]/log n -> c.

It also has the MEAN-SQUARE imbalance limit

    [(1-r)/(-log(1-r))^2]
      * sum_n {[r_B(n+1)-r_C(n)] r^(2(n+1))}^2 -> 0.

Main parity declaration:
Erdos66ParityRepresentation.witness_normalized_parity_imbalance_zero.

## Essential limitation

No separate pointwise self-count limits for B and C have been proved.
The normalized energy can tend to zero while sparse exceptional targets
remain. It therefore does not justify a pointwise coefficient-reduction
operation on a witness, and it remains compatible with the universal
square-root-logarithmic fluctuation lower bound. Neither an infinite
construction nor a contradiction for the original existential statement
has been obtained.
