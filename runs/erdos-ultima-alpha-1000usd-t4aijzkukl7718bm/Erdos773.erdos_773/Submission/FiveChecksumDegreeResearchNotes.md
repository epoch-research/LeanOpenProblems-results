# Exact degree diagnostics for the existing base-five checksum table

The original Erdos 773 conjecture is NOT settled. Spec.lean is unchanged and
still has its sole sorry at line 17287 for 0 < epsilon < 1/3. The verified
actual endpoint remains eventually M(N) >= N^(2/3).

## New clean module

Submission/FiveChecksumDegree.lean imports the clean FiveChecksumExample,
not Spec.lean. It builds without admissions or warnings and has an olean.
All eight printed main audits use only propext, Classical.choice, Quot.sound.
Log: /tmp/five-checksum-degree.log.

Point = Fin 3 -> ZMod 5. Exponent = Fin 3 -> Nat.
A monomial is the product of x_i^e_i. Polynomial expressions are arbitrary
finite sums of such monomials with coefficients in ZMod 5. Exponents are
NOT assumed reduced, so the low-degree obstructions apply to arbitrary
polynomial expressions of the stated total degrees.

## Finite-field summation argument

For k<4, sum_{t in F5} t^k=0, including k=0 because the field has five
points. A monomial with total degree <12 has some exponent <4. Factoring
its sum over the Cartesian grid therefore gives zero. Consequently every
polynomial of total degree at most eleven sums to zero on F5^3.

Similarly, multiplying a monomial of total degree <11 by its second input
coordinate gives total degree <12. Thus the first weighted moment
sum_x x_1 F(x) vanishes for every polynomial of degree at most ten.

## Two checksum conventions, kept separate

The checked root table is originally indexed by r=0,...,124 with

    root(r)=r+1+125*checksum(r).

The canonical-residue convention instead indexes by u=root mod125 and uses

    root=u+125*canonicalChecksum(u).

These are NOT merely input permutations of the same output table: at the
wraparound residue u=0, the change from baseline r+1=125 to baseline u=0
adds one to the checksum value. This distinction matters.

### Canonical-residue convention

canonical_checksum_sum verifies its total sum is 1 in F5. Therefore
canonical_not_low_degree rules out every polynomial representation of total
degree at most eleven. canonical_not_low_degree_after_relabeling proves the
same after ANY bijection of the inputs, and after any affine output change
z -> a*z+b with a nonzero. These transformations preserve a nonzero total
sum on a 125-point grid in characteristic five.

### Original convention in FiveChecksumExample

original_checksum_sum verifies that its total sum is zero.
original_checksum_first_moment verifies

    sum_x x_1 * originalChecksum(x) = 2 in F5.

original_not_low_degree therefore rules out every representation of this
original function by a polynomial of total degree at most ten. No theorem
about arbitrary input permutations of this original convention is asserted.

All numerical moment certificates are checked by the Lean kernel. A Python
interpolation diagnostic initially suggested degrees twelve and eleven,
respectively, but no interpolating polynomial or exact minimal-degree upper
bound is needed or claimed by the Lean results. The formal claims are the
stated lower-degree impossibilities.

## Scope

These statements concern ONE already verified finite Sidon table. They do
not say that all base-five Sidon checksum tables have high degree, that
another cubic rule is impossible, or that all checksum constructions fail.
They provide no unbounded-base family and no exponent amplification. The
existing finite table still does not imply an asymptotic three-quarters
lower bound, much less the original near-linear conjecture.

The accompanying review of square-specific bounded-capacity extraction did
not yield a valid capacity-one selector. Generic capacity obstructions are
still not counterexamples for the actual squares. No new original lower or
upper exponent was obtained. An external direct-IP reference-access attempt
timed out; no mathematical result was retrieved. No numerical/SMT search for
new candidate sets was launched, and no incomplete proof was submitted.
