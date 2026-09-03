# One-step unit-residue lift

This is auxiliary work, not a settlement of Erdős 773. `Spec.lean` remains
unchanged, with its one admission for 0 < epsilon <= 1/3.

## Verified positive statement

`UnitResidueLift.lean` imports only `FormalConjecturesUtil` and proves:

* `pair_sum_lift`: for integers a,b,c,d congruent to r modulo nonzero q,
  if gcd(q,2r)=1 and a^2+b^2=c^2+d^2, then

      q^2 divides a+b-c-d.

* `pair_sum_congruence`: the same result in `Int.ModEq` notation.
* `pairs_identified_of_small_sum_gap`: if additionally
  |a+b-c-d| < |q^2|, the two unordered pairs of roots are equal.

The proof writes each root as r+q*x, cancels q in the square equation,
and uses coprimality to obtain q dividing the difference of index sums.
There is no root-size assumption in the divisibility lemma.

The previously verified `ResidueFibers.unit_progression_squares_sidon`
has a different, stronger size argument for indices in [0,q]: even the
possible nonzero sum gaps of size q contradict ordering of square sums.
The new lemma does not replace that argument.

## Exact limit of the proposed iteration

Define

    A(q) = 2q^2 + 4q + 1,
    B(q) = 9q^2 + 7q + 1,
    C(q) = 6q^2 + 6q + 1,
    D(q) = 7q^2 + 5q + 1.

For every integer q, the file verifies

    A(q)^2 + B(q)^2 = C(q)^2 + D(q)^2,
    A(q)+B(q)-C(q)-D(q) = -2q^2,

and all four roots are 1 modulo q. For q>=2,

    0 < A(q) < C(q) < D(q) < B(q).

For q>=3, q^3 does not divide the pair-sum difference. Thus the common
residue and square-sum equality do not give a third power of q.

This obstruction can be made pairwise coprime, not merely primitive:
for every natural t, take q=9282*t+4641. The theorem
`family_pairwise_coprime` verifies all six pairwise coprimality claims.
`familyModulus_unit` verifies q>=3 and gcd(q,2)=1. The certificates use
small polynomial Bezout identities and the residues modulo 17,7,6,13.
No primality of the roots is asserted. No AP-free claim is asserted.

The identity comes from Gaussian multiplication with factors

    (1+q) + i*(1+2q),
    (1+4q) + i*q,

and conjugating the second factor. The Lean proof checks the resulting
polynomial identity directly with `ring`.

## Scope and verification

This blocks unconditional iteration of the one-step lift, even under
pairwise coprimality. It does not rule out more selective multiscale
constructions, nor does it disprove the main conjecture.

All five printed axiom audits use only propext, Classical.choice, Quot.sound.
The file has no admissions and compiles with

    lake env lean -s 65536 Submission/UnitResidueLift.lean

Log: `/tmp/unit-residue-lift.log`.

No main-gap exponent was improved. The latest main-file check is
`/tmp/spec-unit-residue-check.log`; its one admission is still at line 2031.
No proof submission has been made.
