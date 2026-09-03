# Moment congruences and the primitive-repair gap

The main conjecture is still not settled. `Spec.lean` has not been changed.

## New verified module

`MomentCongruence.lean` imports the clean `SmallSignJets.lean` module. Namespace:
`Erdos773.MomentCongruence`.

1. `neg_one_vanishes`: if V has integer coefficients in {-1,0,1}, degree <D,
   `(X-1)^k | V`, and D<2^k, then V(-1)=0.

   Indeed, |V(-1)|<=D, while (-2)^k divides V(-1). A nonzero value would have
   absolute value at least 2^k.

2. `three_dvd_every_block_multiplier`: under the same hypotheses and k>0,
   `3 | V(2^L)` for EVERY natural block length L. Since V(1)=V(-1)=0,
   `(X^2-1) | V`, and 3 divides `(2^L)^2-1`.

3. `binary_jet_congruence_three`: if two binary-coefficient polynomials of
   suitable length have matching first k jets at one, with D<2^k, their
   evaluations at two are congruent modulo three. The common residue need
   not be zero; in particular this is not an exclusion of prime roots.

4. `cubic_lt_two_pow`: `16*k^3 < 2^k` for k>=17.

5. `three_dvd_cubic_jet_specializations` specializes the factor-three result
   to every signed jet polynomial of degree <16*k^3, for k>=17.

6. `efficient_block_multipliers_not_coprime`: two such polynomials, evaluated
   at possibly different powers of two, have non-coprime natural absolute
   values. Both have the factor three.

All four printed main audits contain only propext, Classical.choice,
Quot.sound. There are no admissions in this module. Log:
`/tmp/moment-congruence.log`.

## Consequences and limitations

The older primitive three-moment construction combined two independently
moment-balanced vectors in one rational rotation plane, using coprime
multipliers from different Mersenne exponents. For the new efficient
high-moment signed-block construction, simply varying the two block lengths
or the signed polynomials cannot supply coprime multipliers once k>=17.
This closes that particular proposed primitive extension.

It does NOT prove that all primitive high-moment collisions are impossible.
It does NOT prove that prime roots in a large moment class have Sidon squares.
The modular congruence alone allows all roots to be in the same nonzero
residue class modulo three. No argument eliminating those four-distinct-root
collisions was obtained.

Further review of modular lifting, polynomial specialization, and recursive
constructions did not yield a main-gap bound. No actual Sidon exponent above
2/3 or fixed-power upper bound was proved. The main file still has its sole
admission at line 2031, for 0<epsilon<=1/3. The latest main compile log is
`/tmp/spec-moment-congruence-check.log`. No proof submission was made.
