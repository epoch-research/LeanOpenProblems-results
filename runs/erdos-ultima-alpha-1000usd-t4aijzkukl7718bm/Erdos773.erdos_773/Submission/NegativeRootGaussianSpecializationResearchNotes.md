# Negative-real-root refinement: exact prime-base obstruction

This does NOT settle Erdős 773. The conjecture and its remaining admission
in Spec.lean are unchanged.

`NegativeRootGaussianSpecialization.lean` imports the clean
`FormalGaussianSidon` module and proves the following exact example.

At the prime base B=509, the four monic cubics

    X^3 + 54 X^2 + 198 X + 6
    X^3 + 396 X^2 + 204 X + 6
    X^3 + 108 X^2 + 66 X + 6
    X^3 + 360 X^2 + 336 X + 6

have positive canonical base digits and common constant coefficient 6.
Every lower coefficient is divisible by six. They are admissible encodings
in the previously proved Gaussian-Eisenstein family, so their formal
squares are Sidon in Z[X].

Each cubic has three distinct negative real roots. This is proved using
exact rational signs at -A, -5, -1/5, 0, where A is the X^2 coefficient.
Three IVT applications give ordered roots x<y<z<0, and an elementary
coefficient argument proves the complete factorization

    f(t)=(t-x)(t-y)(t-z)

for every real t. No approximate root computation enters the proof.

Their integer values are respectively

    145963391, 234572147, 159886577, 225312419,

and the first two squares sum to the last two squares:

    76329403660408490.

The exact formal discrepancy is

    36 X^2 (509-X) (X^2-4X-2).

Thus fixed positive constant, positive canonical digits, negative simple
real roots, admissibility, and primality of the base do not collectively
guarantee Sidonness after specialization. This does not rule out all
subfamilies, all bases, or an arithmetic construction for the original
conjecture.

The module compiles without admissions or warnings, and its eight printed
axiom audits use only propext, Classical.choice, Quot.sound.

Log: /tmp/negative-root-gaussian.log
