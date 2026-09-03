# Finite-field norm checksum investigation

This does NOT settle Erdős 773. Spec.lean is unchanged and still has its sole
sorry for 0 < epsilon <= 1/3. The earlier attempted submission was rejected;
no complete proof or disproof has since been found or resubmitted.

## Motivation and exact scope

A d-free-digit, one-checksum-digit family of square-Sidon roots at height
q^(d+1) would yield exponent d/(d+1), IF it existed at suitable unbounded
scales. No such uniform family is proved. In particular, a fixed q with d
unbounded and only one checksum digit would have constant density, which
is incompatible with the already proved density-zero upper bound.

We screened cubic field-norm checksums in three digits. The norm polynomial
for theta^3=theta+1 is

 N(x,y,z)=x^3+2x^2z-xy^2-3xyz+xz^2+y^3-yz^2+z^3.

The new module NormChecksumExample.lean verifies its determinant identity
for the multiplication matrix [[x,z,y],[y,x+z,y+z],[z,y,x+z]].

## A verified finite success at q=3

Put

 F(a,b,c)=N(a+2+2c,c,b+c)+2a+2,
 r=a+q b+q^2 c,
 n_r=r+q^3 (F(a,b,c) mod q).

The expanded F has positive integer coefficients; checksumPolynomial in
the Lean file uses that expansion, and checksum_norm_formula proves its
identity with the displayed integer norm polynomial.

At q=3 the 27 roots, in residue order, are

 [27,28,29,3,58,59,6,7,62,9,10,38,12,13,68,15,70,44,
  45,73,74,48,22,77,24,79,80].

The file proves their cardinality, interval containment, exact checksum
formula, and square-Sidonness. A sorted list of 378 unordered pairs is
checked in the kernel using SidonPairCertificate; no solver is trusted.

## The SAME formula fails over another genuine cubic field

The file proves X^3-X-1 irreducible over both ZMod 3 and ZMod 13. It also
proves that the checksum formula fails at 13, with the exact values

 r=3     -> 6594,
 r=2058  -> 6452,
 r=8     -> 8796,
 r=585   -> 2782,

 and 6594^2+6452^2=8796^2+2782^2=85109140.

Thus its success at three cannot be promoted to a uniform rule just by
assuming that the defining cubic is irreducible. This does not rule out
other norm/checksum functions, other bases, or large subclasses.

## Exploratory searches (NOT Lean nonexistence theorems)

Research/NormChecksumScreen.cpp checks power-basis norm forms with affine
translations and affine-linear output perturbations. At q=3 its 34992
positive-root candidates all fail. At q=5, with no input translations,
its 100000 candidates all fail.

Research/NormChecksumBases.cpp varies all invertible input bases for a
single cubic field and deduplicates their norm tables. At q=3 there are
288 norm tables and 629856 translated/affine-output candidates. Exactly
one candidate has all 27 roots positive and square-Sidon; it is the
formula certified above. The q=5 full-basis search timed out after 600
seconds with no witness; this is NOT an infeasibility conclusion.

Research/NormChecksumBasesPositive.cpp permits the zero root to be omitted.
Its exhaustive q=3 screen finds eight successful positive-root sets: the
27-root example above and seven 26-root examples. None is asserted to
extend to unbounded scales.

Logs: /tmp/norm-checksum-3.log,
/tmp/norm-checksum-5-no-shift.log,
/tmp/norm-checksum-all-bases-3.log,
/tmp/norm-checksum-positive-3.log,
/tmp/norm-checksum-all-bases-5.log.

## Verification

NormChecksumExample.lean builds cleanly and has an olean. All eight printed
axiom audits use only propext, Classical.choice, Quot.sound (root_formula
uses only propext). Log: /tmp/norm-checksum-example.log.

A concrete large-image membership elaboration was very slow. The final
proof instead uses a generic collision_not_sidon helper before specializing
the function and carrier. The cubic irreducibility proofs need explicit
Fact (Nat.Prime 13), and compute_degree needs the final coefficient proof.

No actual asymptotic lower exponent or upper exponent improved. The
unresolved conjecture and its only import have not been changed.

## Power-of-three continuation

The same exact formula fails at both 9 and 27. These failures are now
proved in NormChecksumExample.lean, not merely exploratory computations.

At q=9:

  r=81 ->4455, r=48 ->2235, r=87 ->4461, r=36 ->2223,
  4455^2+2235^2=4461^2+2223^2=24842250.

At q=27:

  r=248 ->433274, r=146 ->275708, r=286 ->512044, r=32 ->39398,
  433274^2+275708^2=512044^2+39398^2=263741260340.

Theorems: fails_at_nine and fails_at_twentyseven. All ten current principal
module audits use only the permitted axioms. The log and olean were updated;
there are no warnings or admissions. The proof uses norm_num for exact
arithmetic and the existing generic finite collision lemma.

This excludes the blanket claim that the formula works at every power of
three. It does NOT establish failure at all sufficiently large powers,
exclude large Sidon subsets of these carriers, or disprove Erdős 773.
A separate exact formal-polynomial screen for one local linearized tangent
family found no collision among its 729 polynomial words; that finite
screen has not been promoted to a theorem or an asymptotic conclusion.
No new actual exponent was obtained.

## Exact finite energy diagnostics (not an asymptotic theorem)

The same certified norm-checksum formula was reconsidered as a potentially
low-collision carrier, rather than requiring its entire square image to be
Sidon. A q^3-root carrier at height q^4 with only O(q^(3+o(1))) four-root
supports would be useful for a three-quarters-scale alteration argument.
No such estimate was proved.

`Research/NormChecksumEnergy.cpp` counts every unordered pair, including
repeated entries, sorts exact 64-bit integer square sums, and counts pairs
of distinct representations. It separates three-root supports (one pair
is diagonal) from four-root supports. A zero root, if present, is excluded.
The implementation was run only at q=3,5,7,11,13,17,19. These are exploratory
computations, NOT new Lean theorems or proof certificates.

For the original norm formula the (root count, three-root count, four-root
count) values were:

    q=3:   (27,      0,     0)
    q=5:   (124,     1,   122)
    q=7:   (343,     6,   908)
    q=11:  (1331,    8,  7557)
    q=13:  (2197,   15, 16483)
    q=17:  (4913,   16, 54453)
    q=19:  (6859,   18, 87937)

One deterministic-seed random-checksum comparison was also counted at each
base. At the irreducible prime 13 its four-root count was 16200; at 19 it
was 87804. Thus these diagnostics supplied no evidence of the extra power
saving needed by the proposed alteration route. This is NOT a proof that
such a saving is asymptotically impossible, nor does it exclude specially
selected subclasses or different formulas. Log:

    /tmp/norm-checksum-energy.log

The original conjecture remains unresolved. Spec.lean was not changed and
still contains its one admission for 0<epsilon<1/3. No new Lean theorem or
main-gap exponent was established in this review, and no proof was submitted.
