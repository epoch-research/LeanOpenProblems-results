# Arithmetic coordinates for a modified Engel step

This is auxiliary work, not a settlement of Erdős 68.
`ModifiedEngelArithmetic.lean` compiles. Its principal axiom audits list only
propext, Classical.choice, and Quot.sound. Spec.lean is unchanged.

## Exact fractional-linear map

For r>0 set u=1+1/r. If the new denominator is d=B-1 and u<B, then

    r'=r-1/(B-1)>0,
    u'=1+1/r'=((B-2)u+1)/(B-u).

The theorem `inverse_coordinate_update` verifies this identity on the
positive domain. Its integer matrix is

    [ B-2   1 ]
    [  -1   B ],

with determinant (B-1)^2, as verified by `coordinate_determinant`.
For B>=3 the determinant is at least 4. Since the entries include 1, the
matrix itself has no common integral factor that could be cancelled.
This does not rule out every other transformation or a more sophisticated
height argument; it only prevents treating this exact matrix as unimodular.

## Exact cancellation factors in rational coordinates

Write r=a/b with coprime integers a,b. The unreduced updated fraction is

    (d*a-b)/(d*b).

The theorem `common_divisor_iff` proves, for every integer c,

    [c divides d*a-b and d*b]
      iff [c divides d*a-b and d^2].

Equivalently, the two pairs have the same common divisors. The proof is an
explicit Bezout identity and does not assume signs or any unproved gcd bound.
The theorem `new_coprime_denominator` further proves that if b and d are
coprime, the updated numerator and denominator are coprime: no cancellation
occurs at all.

These results do not show that a reduced numerator, denominator, or other
integer height decreases along the target's consecutive multipliers. No
arithmetic exclusion of rational input with all multipliers 3,4,5,... has
been obtained. The original conjecture remains unproved and undisproved in
this work; no proof has been submitted.
