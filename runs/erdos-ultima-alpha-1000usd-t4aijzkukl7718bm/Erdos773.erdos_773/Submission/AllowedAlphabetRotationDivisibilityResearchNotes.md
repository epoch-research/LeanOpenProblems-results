# Exact common modulus and rational-rotation divisibility

The original Erdős 773 conjecture is NOT settled. Spec.lean is unchanged,
with its sole admission at line 17287 for 0 < epsilon < 1/3. The proved
unconditional endpoint remains eventual M(N) >= N^(2/3).

## New verified module

Submission/AllowedAlphabetRotationDivisibility.lean imports the clean
AllowedAlphabetSwapRigidity module. It compiles without warnings or
admissions. All eight printed audits use only propext, Classical.choice,
and Quot.sound.

Log: /tmp/allowed-alphabet-rotation-divisibility.log
Olean: .lake/build/lib/lean/Submission/AllowedAlphabetRotationDivisibility.olean

## Residues of the exact allowed-alphabet family

Write B=6h+7, and use AllowedAlphabetCandidate.root. Every word has digit sum

    C = 3(h+1)(h+2)+1.

`root_mod_base_sub_one` proves root = C modulo B-1.
`digit_sum_coprime` proves gcd(C,B-1)=1: C is odd and C=1 modulo 3(h+1).
The prior fixed constant digit gives root=6 modulo B, and B is coprime to 6.

The sharper common modulus is

    Q = strongModulus(h) = 6 B (B-1).

`root_mod_six`, `root_strong_unit`, and `strong_common_residue` prove that
all candidate roots have the same residue modulo Q, and every root is a
unit modulo Q. The additional factor six comes from the difference formula
for the interior digit sums; it is not obtained by incorrectly multiplying
noncoprime congruences.

For h>=2, `common_modulus_iff` proves, for EVERY integer T,

    (all candidate roots have one common residue modulo T)
      iff T divides Q.

An adjacent swap of consecutive digits in the identity permutation gives
an actual root difference exactly Q. Thus this is an exact maximal-common-
modulus result, not just a convenient divisor of the differences.

## Generic rotation consequence

Suppose x,y,z,w share a unit residue modulo an integer Q, and BOTH rows hold:

    q*z = p*x+s*y,
    q*w = -s*x+p*y.

`rotation_coefficients` proves Q divides 2s and Q divides 2(q-p).
There is no primality or odd-modulus hypothesis. The conclusion is about
TWICE each coefficient; it does not say each coefficient is an even multiple
of Q.

If p=m^2-n^2, s=2mn, q=m^2+n^2 and IsCoprime m n, then
`rotation_parameter` proves Q divides 4n, by an explicit Bezout combination.

`candidate_rotation_lower` applies this to the exact candidate and, when
n is nonzero, proves

    Q divides 4n,
    Q <= 4|n|,
    Q^2 <= 16(m^2+n^2).

The displayed denominator is the parameter denominator m^2+n^2. The theorem
does not claim it is already reduced when both parameters are odd.

## Scope and remaining gap

Both actual rotation equations and coprimality of m,n are explicit
hypotheses. This module does not silently identify a matching-oriented
rotation with a small Gaussian factor, whose normalization may involve
sign changes or coordinate swaps. No universal small-factor transfer is
asserted here.

The older CompositeResidueRotation module already proves related two-row
restrictions for odd moduli. The new work identifies the exact candidate's
common unit residue modulus, includes its even factors, and proves that no
larger common modulus is available from the full permutation carrier.

The cutoff is only polynomial in B, whereas the candidate root height has
order B^(h+1). No useful estimate for the surviving large-parameter
collisions, no eventual Sidon theorem, and no improved unconditional
exponent were obtained. This is not an original-conjecture disproof.

The generic bounded-capacity route was rechecked: its verified ordinary-
integer counterexamples have a uniform bound for EVERY positive difference,
so uniformity alone does not repair that rounding argument. Those examples
are still not square-set counterexamples. External references remained
unavailable (DNS and direct-IP HTTPS both failed).

No incomplete proof was submitted.
