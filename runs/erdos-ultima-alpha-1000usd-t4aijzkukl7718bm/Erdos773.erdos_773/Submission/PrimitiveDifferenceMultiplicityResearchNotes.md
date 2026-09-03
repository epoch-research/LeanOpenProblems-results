# Primitive and globally pairwise-coprime difference families

This does NOT settle Erdős 773 or improve the main-gap exponent. `Spec.lean`
is unchanged, and no incomplete proof has been submitted.

## Verified results

`PrimitiveDifferenceMultiplicity.lean` proves two main statements:

1. For every k, some positive D has at least 2^k positive representations
   b^2-a^2=D with a<b<=D and gcd(a,b)=1.

2. More strongly, for every k there exist a positive D, a root set S of
   cardinality 2^(k+1), and 2^k distinct pairs (a,b) from S, such that
   0<a<b, b^2=a^2+D, and ALL distinct roots in S are pairwise coprime.

The second assertion is stronger than merely taking a primitive four-root
collision or assuming coprimality separately within each pair. No primality
of the individual roots is asserted.

## First construction

Start with the odd coprime factor pair (1,3). Given a family u*v=D of odd
coprime factors with u<v, put p=2D+1, which is coprime to D. Replace each
pair by (u,p*v) and (v,p*u). Both new pairs are ordered and coprime, and the
two images are disjoint. This doubles the family at each step. Mapping a
factor pair to ((v-u)/2,(v+u)/2) gives positive coprime root pairs of
square difference D.

## Global coprimality construction

Take any of the finite odd coprime factor families u_i*v_i=F above. For an
even positive integer x, consider the two roots

    v_i*x-u_i,   v_i*x+u_i.

Their square difference is the common value 4*F*x. All signed linear forms
v_i*X +/- u_i have pairwise nonzero determinants: equality of two positive
ratios u_i/v_i would identify their factor pairs, and opposite signs cannot
give equal nonzero ratios.

Let T be the finite set of prime divisors of these nonzero determinants
which do NOT divide F, and take x=2*product(T). Then x is coprime to odd F.
If a prime divided two root values, it would divide their determinant.

* If it divided F, coprimality of u_i,v_i and of x,F prevents it from
  dividing even one root value.
* Otherwise it belongs to T and divides x. Dividing a root value would then
  force it to divide u_i, hence F, a contradiction.

All root values are at least two, so their pairwise coprimality also makes
them distinct. The theorem verifies the exact cardinalities of the resulting
root and pair sets.

## Scope and verification

These results rule out a CONSTANT multiplicity bound based solely on either
form of coprimality. They do not refute subpower bounds, supply a fixed-power
upper bound on the square-Sidon maximum, or preclude a better compatible root
selector. In particular, no useful near-linear relation between family size
and largest root is asserted.

The complete module compiles without warnings. Both printed main axiom
audits contain only propext, Classical.choice, and Quot.sound.
Log: `/tmp/primitive-difference-multiplicity.log`.
