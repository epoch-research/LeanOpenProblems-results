# Full ordinary alphabet: a finite carry obstruction

This is NOT a settlement of Erdős 773. Spec.lean remains unchanged with its
sole admission for 0 < epsilon <= 1/3. No proof submission has been made.

## What was tested

The continuation revisited the transfer from formal polynomial identities
to evaluation at an integer base. The previous Gaussian Eisenstein and
small-total-digit-sum failures were checked before considering a different
candidate: permutation words using the entire ordinary base alphabet.

An exact finite screen of this candidate found a counterexample at base 8
even with the leading digit fixed to 1 and the constant digit fixed to 3.
The final Lean theorem does not depend on the exploratory Python output.

## Verified words and values

File: FullAlphabetCarryObstacle.lean

Digits, constant coefficient first:

  [3,5,7,2,6,4,0,1] -> 2254315
  [3,6,4,2,7,0,5,1] -> 3437875
  [3,4,7,6,2,5,0,1] -> 2272739
  [3,7,6,2,4,0,5,1] -> 3425723

Each word is a bijection Fin 8 -> Fin 8, so every digit 0,...,7 appears
exactly once. Every word has constant digit 3 and leading digit 1. The
nontrivial collision is

  2254315^2 + 3437875^2 = 2272739^2 + 3425723^2
                       = 16900920634850.

Public theorem full_alphabet_family_not_sidon states that the square values
of ALL full-alphabet base-eight words with those fixed end digits are not
Sidon. The proof embeds the four verified words into that family.

## Formal polynomial certificate

Writing P_i(X) for the displayed digit polynomials, Lean also proves

  P0^2+P1^2-P2^2-P3^2
    = -X^2 (X-8)(X-1)
        (2X^8+4X^7+7X^6+7X^5+6X^4+10X^3+10X^2+8X+2).

Thus this is an integer-evaluation collision, not a formal polynomial norm
identity. In particular, the same four words are not asserted to collide
at other integer bases.

## Scope: important distinctions

* This refutes a blanket sufficient criterion based solely on full ordinary
  alphabet permutation words, even with these fixed end digits.
* It does NOT exclude a large Sidon subclass of that family.
* It does NOT show failure at every sufficiently large base.
* These lower digits are NOT all divisible by 3. This is not a counterexample
  for a complete alphabet consisting only of the allowed Eisenstein digits.
* Using the entire ordinary alphabet necessarily includes digits above half
  the base; do not conflate this with the earlier half-base digit conditions.
* No original-conjecture upper or lower exponent was improved.

## Verification

All seven printed audits use only propext, Classical.choice, Quot.sound
(some use fewer). No warnings, admissions, or untrusted computation remain.
Finite certificates use ordinary trusted `decide +kernel`; the polynomial
identity is checked with `ring`.

Build: .lake/build/lib/lean/Submission/FullAlphabetCarryObstacle.olean
Log: /tmp/full-alphabet-carry-final.log
Main check: /tmp/spec-full-alphabet-check.log

Spec.lean hash remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
