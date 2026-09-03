# Fixed logarithmic coefficient for growing finite-field extensions

## Original task status

The conjecture in `Submission/Spec.lean` remains unproved and undisproved.
Its statement, import, and original `sorry` are unchanged. No proof or
disproof was submitted.

## New verified files

* FiniteFieldDegreeExplore.lean
* OddDegreeLogTuningExplore.lean
* LogTunedGrowingFieldExplore.lean

All three compile with current oleans and no warnings. The five declarations
in `LogTunedFieldExtensionAudit.lean` use only `propext`, `Classical.choice`,
and `Quot.sound`; the saved audit log records this. There are no production
placeholders or new axioms. `FiniteExtensionChecks.lean` is only an API-search
scratch file and intentionally contains failed checks.

## Actual extension fields, not assumed degree availability

`exists_extension_degree` constructs an actual field type K with an F-algebra
structure for every finite field F and every positive integer d. It proves

    [K:F]=d,   |K|=|F|^d,   char(K)=char(F).

The construction uses a Galois field over the prime field, the verified finite
field embedding criterion, and multiplicativity of vector-space dimension.

## Explicit odd-degree tuning

For q>=2, u>=0, c>0, put mu=(u+q)^2 and L=log q. The selected degree is

    d = 2 ceil(mu/(4cL)) + 1.

It is odd and at least three, and satisfies

    0 <= c - mu/log((q^d)^2) <= 6c^2 log(q)/q^2.

The upper bound tends to zero as q tends to infinity. Thus the new mean is
compared with the logarithm of the actual NEW field-plane cardinality.
There is no hidden replacement of log(|K|^2) by log(|F|^2).

## Fixed coefficient and precision before the old field

`exists_log_tuned_growing_extension` has the following quantifier order:

For c,delta>0, first choose epsilon in (0,1] and N. Then for ANY finite
odd-characteristic field F with q=|F|>=N, and any old repaired model

    parabolaSet(U) union repairPoints(w,T),

satisfying the explicit nonzero/no-opposite, nonempty, unused-w/-w, and
zero-free-T hypotheses, together with

    10|U| <= epsilon q,

there are an actual larger field K, its field/Fintype/decidable equality/
F-algebra structures, and an actual finite set B in K^2 such that:

* [K:F] is odd and |K|>=q^3;
* B's old field-plane slice is EXACTLY the prescribed old repaired model;
* at EVERY field-plane target z, including zero,

      |r_B(z)/log(|K|^2)-c| <= delta.

The proof uses epsilon=min(1,delta/(2c)). The threshold supplies both
1600<=epsilon^2 q and tuning cost <=delta/2. The scalar normalization lemma
retains the factor mu/log(|K|^2)<=c, so the final error is at most
c epsilon+delta/2<=delta.

## Remaining gap and carry review

This removes the finite-field logarithmic tuning gap for the growing-slice
construction. It is still NOT a proof of the original conjecture:

* Counts here use the additive group of K^2, not ordinary integer addition.
* Exact old membership does not preserve field-group representation counts
  at old targets; new endpoints can cancel in the group.
* The available ordinary-carry operators use fixed prime-field/color data.
  They do not transfer this extension-field construction with compatible
  natural prefixes and the required density/error bounds.
* Every intermediate natural-number prefix remains uncontrolled.
* No infinite natural set, or finite-prefix feasibility with the original
  quantifiers, has been constructed.

In particular, global field-plane flatness cannot simply be identified with
flatness of a witness's full cyclic prefixes: the old `CyclicPrefixExplore`
results already show a fixed variation in those cyclic prefixes. A genuine
inhomogeneous ordinary-addition transfer is still needed.

## Subsequent natural-window mass check

See `CosetWindowObstructionProgress.md`. A plain coset-by-coset encoding of
the new O(q)-parameter models has too few points in the first square-sized
doubling window. That specific transfer route is now excluded by a checked
mass bound, not just left without a carry estimate. Other encodings and
larger parameter families remain outside that obstruction.
