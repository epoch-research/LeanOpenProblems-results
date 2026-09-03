# Explicit columnwise falling-residue forms

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged.

## Verified family

`FallingResidueForms.lean` compiles without warnings and its olean is built.
The three principal axiom audits contain only propext, Classical.choice,
and Quot.sound. There are no proof holes in this auxiliary file.

For j>=1 put

    E_j = sum_(n>=2) 1/(n!)^j,
    A_j = 6^j - 2*2^j + 1,
    B_j = 3^j - 1.

The verified `remainder_sum`, `column_form_bounds`, and
`tendsto_column_forms` give

    0 < A_j E_j - B_j < (3/2)/2^j,
    A_j E_j - B_j -> 0 as j -> infinity.

The formal index r is j-1. The summand used in the proof is

    1/(k+2)!^j - 2*2^j/(k+3)!^j + 6^j/(k+4)!^j.

After multiplication by (k+4)!^j its numerator is

    ((k+4)(k+3))^j - 2(2(k+4))^j + 6^j > 0.

A general strict convex-power inequality proves this positivity by induction.
The summand is also strictly less than 1/(k+2)!^j, giving the uniform bound.

## How the family arose (external exact polynomial calculation)

Let L_j H(n)=n^j H(n-1)-H(n), and r_N(n)=(n-2)...(n-N-1).
Reducing r_N(n)*s(n) modulo the image of L_j, with deg s<j, gives a
j-dimensional rational linear system. Exact calculations for 1<=j<=4
and 1<=N<=8 were completed in `/tmp/falling_residue_systems.py`, with
output `/tmp/falling_residue_systems.log`. These finite calculations are
not themselves Lean-verified.

The general formulas suggested by, and derivable from, interpolation are

    D_(N,j) = sum_(k=0)^N (-1)^(N-k) choose(N,k) ((k+1)!)^j,
    C_(N,j) = sum_(k=0)^N (-1)^(N-k) choose(N,k)
                 sum_(m=2)^(k+1) ((k+1)!/m!)^j.

Both are integers. Their residual is the Nth finite difference of the
scaled factorial-power tails. At N=2 these are exactly A_j and B_j above.
Only the N=2 family and its bounds are asserted by the new Lean file.

## Remaining arithmetic gap

These are integer linear forms in E_j, NOT in the single fixed number
alpha=sum_(j>=1) E_j. The target varies as j tends to infinity. Rationality
of alpha does not make A_j E_j-B_j integral after multiplication by a
fixed denominator. The leading coefficient A_j also varies with j;
summing these forms does not produce A*alpha-B with integral A and B.

Thus the new infinite family does not prove the conjecture. No common-
leading-coefficient construction with a controlled integral total boundary
has been obtained, and no complete proof or disproof has been submitted.

## Subsequent verified clearing obstruction

`FallingBoundaryBarrier.lean` now proves that clearing even the last
individual normalized boundary forces a multiplier greater than 2^J,
and makes the resulting positive error against alpha exceed one. This
includes reducing that individual boundary first, but not arbitrary
cancellation in the aggregate boundary. See FallingBoundaryBarrierNotes.md.
