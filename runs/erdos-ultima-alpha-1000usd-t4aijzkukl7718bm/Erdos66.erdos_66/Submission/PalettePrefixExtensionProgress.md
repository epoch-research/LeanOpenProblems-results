# Prefix-preserving extensions within a fixed joint palette

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Submission/Spec.lean is
unchanged with its original sorry. No proof has been submitted.

## Prescribed old pieces are kept exactly

PalettePrefixExtensionExplore.lean proves

    exists_prefix_preserving_quantized_extension.

Fix a modulus M and a joint endpoint-prefix-balanced palette P. Let a finite
index family s describe disjoint intervals [a_i,b_i) inside [0,M), with
positive desired heights w_i>=1. Suppose palette coverage can choose each
cardinality between w_i|B| and (1+epsilon)w_i|B|.

An arbitrary subset old of the indices is prescribed FIRST. For each old
index, its member D_i is also prescribed FIRST, subject only to membership
in P and the required cardinality bracket. Assume old intervals end at or
before L and new intervals start at or after L.

The theorem chooses only the remaining palette members and returns A with:

* A is contained in [0,M);
* the entire prescribed old assembled set is contained in A;
* membership below L agrees exactly with the prescribed old set;
* every representation count below L is exactly unchanged;
* every added point is at least L;
* for n<2L, the exact increment is twice the old/new mixed pair count;
* the same all-target step-profile error bound holds:

      |r_A(n)-mu F(n)|
        <= [(1+2 eta)(1+epsilon)^2-1] mu (sum_i w_i)^2.

Here mu=actualMean(M,B,B) and F is the geometric overlap profile defined in
IntegerPaletteQuantizationExplore.lean. No old piece is reselected in the
proof. This is stronger than merely obtaining an unrelated accurate finite
set, but it applies only to the specified structural class of old prefixes.

## Unconditional finite extension systems

BoundedWeightPaletteExplore.lean ensures that an arbitrarily large balanced
complete palette has enough cardinality range for any fixed multiplier W.
The proof combines the logarithmic sparse mean with log(M)/M -> 0.

LogarithmicPrefixSystemExplore.lean proves

    exists_logarithmic_prefix_extension_system.

For fixed finitely many heights w_i>=1, c>0, and delta>0, it chooses a single
precision t>0 BEFORE an arbitrary lower modulus bound. At arbitrarily large
M there are B and P such that EVERY subsequently prescribed old family as
above admits a prefix-preserving extension satisfying

    |r_A(n)/log M-c F(n)| <= delta      for every natural n.

The old index subset, interval geometry, cutoff L, and old members D_i are
all quantified after M and P; the new choices are made only after those.
The precision can be taken as

    t = min(1, delta/[100(c+1)((sum_i w_i)^2+1)]).

A separate normalized_weighted_error lemma handles mean tuning. The system
retains exact old membership and old representation counts, not merely an
approximation to them.

## Verification

All three new production files compile and have built oleans:

* PalettePrefixExtensionExplore.lean
* BoundedWeightPaletteExplore.lean
* LogarithmicPrefixSystemExplore.lean

PalettePrefixExtensionAudit.lean audits the principal declarations. Only
propext, Classical.choice, and Quot.sound occur. The production files
contain no sorries or new axioms.

The attempted external reference lookup failed because network name
resolution is unavailable; no new external mathematical result was used.

## What remains missing

The palette and its modulus are selected BEFORE the admissible old prefix.
This supplies robust prefix preservation within ONE finite system, not a
way to transfer an existing natural-number prefix into an unrelated later
system. The fixed heights and the number of pieces still determine the
precision and modulus threshold.

In particular, the theorem does not justify iterating outer repetition,
replacing the modulus, or taking compactness with cutoff-independent
thresholds. Arbitrary short-prefix patching of cyclic templates does not
repair this issue: its global error does not become a useful local estimate
at targets comparable to that patched prefix. No compatible infinite chain
of the systems, and no universal negation of the conjecture, is proved.
