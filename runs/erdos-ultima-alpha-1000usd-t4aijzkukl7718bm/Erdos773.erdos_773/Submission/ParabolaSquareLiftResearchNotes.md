# Carry-aware parabola lifting

This continuation does NOT settle Erdős 773. The main file is unchanged and
still has its sole admission for 0 < epsilon <= 1/3.

## New verified module

`ParabolaSquareLift.lean`, namespace `Erdos773.ParabolaSquareLift`, imports the
clean `MatchedResidueLifting` module, not the admitted main file.

For an odd prime p and a label 1 <= b < p, define

    a_b = ((b - floor(b^2/p))/(2b) in ZMod p).val,
    r_b = b + p*a_b,
    T_b = (b^2 mod p) + p*b.

The verified lemmas show

    0 < r_b < p^2,
    r_b mod p = b,
    gcd(p^2, 2*r_b) = 1,
    r_b^2 = T_b modulo p^2.

The lift is injective on canonical labels.

A carry issue must be handled before invoking the prime-field parabola:
the low and high base-p digits do NOT add independently. Partition the labels
by whether 2*(b^2 mod p) < p. For labels in one part, two congruent sums of
low digits must be equal as integers: both sums lie in the same interval of
length p. Cancelling this equality in a congruence modulo p^2 gives the
root-label pair sum modulo p. Together with the square-label pair sum, this
identifies the unordered pair in the field ZMod p.

Consequently `exists_pair_matching` proves that for every odd prime p there
is a canonical unit root set R with

    2*|R| >= p-1,
    PairMatching (p^2) R.

Other public results include `pair_eq_of_sum_and_square_sum`,
`root_square_congruence`, `same_half_sum`, `target_pair_matching`,
`lift_pair_matching`, `lift_card`, and `root_unit`.

This is a modular construction of square-root size at root height p^2.
It is NOT a near-linear integer construction and does not improve the actual
2/3-o(1) Sidon lower exponent.

## The next full-fiber step does not follow

At p=3, both nonzero labels belong to the lower half-band, and

    r_1=7, r_2=5.

`three_lift_image` verifies that the lifted set is exactly {5,7}.
`full_fiber_obstruction` verifies both PairMatching 9 {5,7} and failure of
Sidonness for all full index fibers 0,...,9 over these two residues. The exact
collision is

    41^2 + 43^2 = 7^2 + 59^2 = 3530.

The root indices are (r,i)=(5,4),(7,4),(7,0),(5,6), respectively. Thus the
obstruction occurs in the actual parabola lift, not in an unrelated modular
example. The individual unit fibers are covered by the existing within-fiber
Sidon theorem; their union still requires cross-fiber compatibility.

The existing `criterion_card_ceiling` applies to arbitrary positive q,
including q=p^2, if its extra ShortProducts hypothesis is supplied. The
parabola construction does not supply that hypothesis. No unrestricted
prime-power full-fiber ceiling has been proved in this continuation, and no
claim about arbitrary partial fibers or the original maximum is made.

## Verification

    lake env lean -s 65536 \
      -o .lake/build/lib/lean/Submission/ParabolaSquareLift.olean \
      Submission/ParabolaSquareLift.lean

All seven printed audits use only propext, Classical.choice, and Quot.sound.
There are no admissions or warnings in the new module. The finite example
uses trusted `decide +kernel`, not native evaluation.

Log: /tmp/parabola-square-lift.log.
Main-file check: /tmp/spec-parabola-lift-check.log.
No incomplete proof has been submitted.
