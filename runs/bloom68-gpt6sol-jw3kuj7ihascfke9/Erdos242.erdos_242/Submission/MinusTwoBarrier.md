# The forced `p−2` factor cannot be the full Type-II modulus

**Status: partial obstruction, not Erdős–Straus.** `MinusTwoBarrier.lean`
contains a sorry-free proof of the statements below. It imports
`AdjacentFactor.lean`, not `Spec.lean`; the specification is unchanged. It
neither supplies a witness for every hard prime nor produces a bad prime.
The condition throughout is the **full** `d∣m²`, not the smaller `d∣m` axis.

## A forbidden exact residue despite the permissible Jacobi sign

For every `m≥2`, every positive divisor `d∣m²`, and `h=4m−1`,

    h ∤ 2+4d.                                                   (1)

**Proof.** Set `e=m²/d`. If `h∣2+4d` and `2+4d=h t`, then reduction
modulo 4 gives `t≡2 (mod 4)`: either `t=2` or `t≥6`. The exact duality
identity

    4e(2+4d)=(8e+1)+h(4m+1)

also yields `h∣8e+1`; in particular `2m−1≤4e`. If `t=2`, then
`d=2m−1`. As `d∣m²`, the identity
`4m²=(2m−1)(2m+1)+1` implies `d∣1`, contrary to `m≥2`. If `t≥6`,
then `d≥6m−2`; multiplying the two lower bounds gives

    4m²=4de ≥ d(2m−1) ≥ (6m−2)(2m−1)
        =4m²+2(4m−1)(m−1)>4m²,

again impossible. The exception `m=d=1`, `h=3`, does satisfy `3∣6`.
These inequalities and the exact duality are checked in
`no_two_modular_divisor`. The congruence statement for any `p` with
`p≡2 (mod h)` is `no_modular_divisor_if_two_remainder`.

For `m` odd, `h≡3 (mod 8)`, so the Jacobi symbol `(2/h)=−1` is
**exactly the sign required** by the full Type-II modular axis. Thus (1)
exhibits a real *divisor-residue* obstruction not detected by the
quadratic sign. As a small instance, `m=3`, `h=11`, and `p=409`
satisfy `p≡2 (mod 11)` and `(p/11)=−1`, but none of `d=1,3,9`
hits `11∣p+4d`. The prime 409 has other solutions; this is only one
failed modulus.

## Consequence for a forced factor of a hard prime

If `p=24k+1`, `k>0`, and `h=4m−1` divides `p−2`, then **no**
`d>0`, `d∣m²` can make `h∣p+4d`. For `m≥2`, simply substitute
`p≡2 (mod h)` into (1); for `m=1`, `h=3` does not divide `p−2`
because `p≡1 (mod 3)`. This is the Lean theorem
`hard_modular_modulus_not_dvd_p_minus_two`, and does not even require
primality. In particular the forced prime factor `3 (mod 4)` of
`p−2≡3 (mod 4)` from `ForcedFactorAudit.lean` cannot be recycled
*as the modulus `4m−1` of a full Type-II modular certificate*, even
if its size is acceptable. It says nothing about choosing that factor
as the *first-denominator modulus* `a=4x−p`, or about other Type-I/
Type-II witnesses.

## The pointwise task this does not solve

For each **prime** `p=24k+1`, `CoveringGap.all_good_iff_explicit_hard_cover`
requires an actual index `0≤j<6k`, `x=6k+1+j`, `a=4j+3`, with either

    c>0, c∣x², a∣4c+1;     or     0<d<x, d∣x², a∣x+d.        (2)

Theorem (1) excludes one tempting modulus family in the Type-II
parametrization; it does not cover the remaining moduli, force (2) at
any `j`, or exclude (2) at *all* `j` for a prime. In particular, the
soluble prime `2521` has `11∣2519=p−2` and therefore no Type-II modular
witness at `m=3`, but `(m,d)=(12,16)` does work at a different modulus:
`47∣2521+4·16`. Nor may a finite scan or density argument be used to
upgrade this local obstruction to a universal assertion.

Verified with `lake env lean Submission/MinusTwoBarrier.lean` and
`lake build Submission.MinusTwoBarrier`. A `#print axioms` audit for the
three named declarations lists only `propext`, `Classical.choice`, and
`Quot.sound` (no `sorryAx` or new axioms). No edit or import of
`Submission/Spec.lean` is involved.
