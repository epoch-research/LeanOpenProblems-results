# Exact row-factor division can lose boundary integrality

Verified auxiliary work, NOT a proof or disproof of Erdős 68. Spec.lean is
unchanged with its original sorry. No settlement has been submitted.

`LambertFactorDivisionBoundary.lean` compiles without warnings, has a built
olean, and contains no proof holes. Its principal axiom audit lists only
propext, Classical.choice, and Quot.sound.

## Exact example in the actual Lambert prefixes

Write S_n=prefixQ(n), the rational prefix of the actual Lambert factorial
series. Take C=26611200 and the row factor 6 E^3-1. Lean verifies

    C*(6*S_10-S_7) = 165160732,
    C*(6*S_11-S_8) = 163450676,
    C*(6*S_12-S_9) = 165957261,

but

    C*S_9 = 94996000/3,

which is not an integer. Thus every phase in the full period n=7,8,9 of
the factored output is integral, but the same multiplier does not clear
the quotient's boundary throughout that period.

The theorem `exact_factor_division_loses_integrality` states this directly
using the existing actual `boundary [3]` and `boundary []` definitions.
The arithmetic is kernel-checked: finite natural Lambert coefficients use
`decide`, the rational identities use `norm_num`, and nonintegrality is
proved by reducing to 3*z=94996000 in integers. No external numerical
result is imported as a premise.

## Scope

The exact coefficient-height reduction in LambertAnnihilatorHeight remains
valid. It does not by itself provide integrality after quotienting, even
when the factored output has a complete period of cleared phases. The
example is finite; it does not rule out a separate asymptotic transfer with
additional hypotheses or a controlled extra multiplier.

An exact rational exploratory check considered row degrees 2 through 10 to
identify this transfer failure; the displayed degree-three instance is the
one verified in Lean. All checks have completed. No original-conjecture
proof, infinite nonvanishing statement, or useful bounded-lift theorem was
obtained. Nothing remains running or pending compilation.
