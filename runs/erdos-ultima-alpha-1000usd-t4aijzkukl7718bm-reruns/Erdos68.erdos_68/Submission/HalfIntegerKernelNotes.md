# Half-integer-root monic remainder kernels

This is a new mathematical construction and an independently audited exact
finite test, NOT a Lean-verified settlement of Erdős 68. Spec.lean remains
unchanged with its original sorry. No complete proof or disproof has been
obtained or submitted in this continuation.

## Family with the existing integer-boundary mechanism

Write

    R_k(x)=product_(j=1)^k(x+j)-1,
    P_N(x)=product_(j=1)^N(2x+2j+1).

Let s_4=sum_(k=1)^4 1/R_k(1), C=den(s_4)=13685. Define integers

    A_N=C*P_N(1),
    B_N=C*sum_(k=5)^N (P_N div R_k)(1) + C*s_4*P_N(1).

Here the quotients are by monic integer polynomials. The exact identity is

    A_N*alpha-B_N
      =C*sum_(k>=5) (P_N mod R_k)(1)/R_k(1).

This is an immediate finite-prefix variation of the previously verified
RisingMonicForms integer-form identity. The variation and the following
root argument have NOT been separately formalized in Lean.

## All-index sign argument (mathematical, not Lean-verified)

For k>=5, R_k has one simple real root rho_m in each cell
(-m-1/2,-m+1/2), 1<=m<=k. Here is an elementary proof.

At x=-m its value is -1. At

    x=-m+(-1)^(m-1)/2

the product F_k=R_k+1 is positive: it has m-1 negative factors if m is odd,
and m negative factors if m is even. Its absolute value is greater than
one. Indeed its factors are distinct signed half-integers. Each absolute
half-integer value can occur at most twice. The five smallest possible
absolute factors are therefore bounded below by

    1/2, 1/2, 3/2, 3/2, 5/2,

whose product is 45/32>1; every remaining factor is at least 5/2. The
intermediate value theorem gives a root strictly between -m and the
chosen half-integer endpoint. The k disjoint cells give k distinct roots
of a degree-k polynomial, hence all roots and their simplicity.

Order these roots from right to left. For k<=N, both P_N(rho_m) and
R_k'(rho_m) have sign (-1)^(m-1). For P_N this follows by counting the m-1
half-integer zeros to the right of rho_m. For R_k' it follows from the
factorization into its k distinct real roots. Moreover 1-rho_m>0.
Lagrange interpolation of the remainder T=P_N mod R_k gives

    T(1)/R_k(1)
      =sum_(m=1)^k P_N(rho_m)/[(1-rho_m)*R_k'(rho_m)] > 0.

For k>N, the remainder is P_N itself, also positive at one. Thus the
infinite form is strictly positive for every N. This sign argument does
not bound its size after integral or primitive normalization.

## Completed exact test

Construction: /tmp/half_integer_kernel.py
Output:       /tmp/half_integer_kernel.log
Certificates: /tmp/half_integer_kernel.json

For N=1,...,80, the script divides the integer polynomial by every R_k
with 5<=k<=N, checks each quotient/remainder identity, and checks positive
remainder evaluations at one. It constructs (A_N,B_N), divides the pair
by its gcd, and evaluates the reduced form against the FULL target.

The enclosure uses W=500! and

    L=sum_(d=2)^500 floor(W/(d!-1)),
    L/W < alpha < (L+502)/W.

All 80 primitive integer errors are strictly greater than one. At N=80,
the reduced retained coefficient has 477 bits and the reduction gcd has
21 bits. No floating-point sign or magnitude test is used.

## Independent audit

Script: /tmp/half_integer_kernel_audit.py

The audit reconstructs the polynomial coefficients and computes every
boundary through reciprocal Laurent-series recurrences, rather than Sage
polynomial division. It separately recovers every remainder evaluation
from those quotient values. It checks all raw and reduced pairs, gcds,
bit counts, and positive finite remainders. It also checks the rational
midpoint inequalities used above for every k=5,...,80 and each root cell.

For the full-target error it uses the different grid W=520!, verifies that
its intervals lie within the stored construction intervals, and verifies
that every lower endpoint exceeds one. All 80 audits passed.

## Scope

This test is not an asymptotic impossibility theorem. The all-index
positivity argument provides nonvanishing, but no primitive-height bound
or growing family of errors tending to zero was obtained. The finite
tests do not supply the missing infinite estimate. The original conjecture
remains unresolved, with no compilation, computation, or audit pending.

## Subsequent Lean verification of the infinite sign argument

The root-location and all-index positivity arguments above are now verified,
not merely finite numerical observations. Two new auxiliary files compile
without warnings and have built oleans:

* Submission/RisingHalfIntegerRoots.lean
* Submission/HalfIntegerPositive.lean

They contain no proof holes. Every printed principal axiom audit contains
only propext, Classical.choice, and Quot.sound. Spec.lean is unchanged.

### Root cells

`root_in_cell` proves that for k>=5 and 1<=m<=k, the real evaluation of
R_k has a root strictly between -m-1/2 and -m+1/2. The proof verifies the
half-integer product bound by splitting it into two rising products from
1/2, handles their signs, and applies the intermediate value theorem.

`root_enumeration` constructs an injective family indexed by Fin k in
these cells and proves that the mapped polynomial's entire root multiset
is exactly that family's finite image. In particular these are all its
roots, with no multiplicities.

### Positive remainders and the full-target form

`HalfIntegerPositive.kernel N` is the integer polynomial P_N above.
`kernel_natDegree` verifies its degree N. `remainder_eval_pos` proves

    0 < (P_N mod R_k)(1),  5<=k<=N.

The Lean proof uses Lagrange interpolation but avoids an explicit derivative
sign calculation: it pairs each half-integer polynomial factor with the
corresponding node-difference factor. Both are negative to one side of the
selected node and positive to the other, so every paired factor is positive.
The remaining numerator factors are also positive. The degree bound and
exact evaluation of a monic remainder at each root give the interpolation
identity.

`residueRow_pos` extends positivity to EVERY k>=5, including k>N where the
quotient vanishes. The finite exceptional prefix is evaluated exactly:

    s_4 = 17132/13685.

The definitions `retained` and `integralBoundary` give precisely the integer
pair displayed at the start of this note. `integer_form_identity` retains
the complete infinite tail, and `integer_form_pos` proves its strict
positivity for every N. No rationality of the target is assumed.

### A verified limitation before pair reduction

`unreduced_error_gt_nineteen` proves the stronger uniform inequality

    19 < A_N*alpha-B_N,  for every N.

The first retained row has denominator 6!-1=719 and a positive INTEGER
remainder numerator, hence contributes at least 1/719. Every later row is
positive. Multiplication by 13685 gives a lower bound 13685/719>19.

This is a bound on the UNREDUCED pair. It must not be applied after dividing
both coefficients by an unbounded gcd. The exact finite primitive-pair tests
above still show errors greater than one only in their tested range.
No asymptotic bound making the primitive errors tend to zero, or otherwise
settling the original irrationality conjecture, has been proved. All builds,
axiom checks, and computations in this continuation have finished.
