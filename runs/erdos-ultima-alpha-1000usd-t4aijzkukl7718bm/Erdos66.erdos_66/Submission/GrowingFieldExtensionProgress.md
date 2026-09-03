# Growing finite-field parameter blocks with exact old slices

## Original task status

The conjecture in `Submission/Spec.lean` is still neither proved nor
 disproved. The target is unchanged and retains its original `sorry`.
No proof was submitted. These are finite-field results, not a transfer to
ordinary natural-number representation functions.

## Verified files

* GrowingParameterTranslateExplore.lean
* GrowingFieldSliceExplore.lean
* GrowingOriginRepairExplore.lean
* GrowingSubfieldBlockExplore.lean

All four compile with current oleans and no warnings.
`GrowingFieldExtensionAudit.lean` audits 26 lemmas/theorems; its saved log
uses only `propext`, `Classical.choice`, and `Quot.sound`.
There are no new axioms or placeholders in these production sources.

## 1. A fresh low-energy parameter block

Let K be a finite field of odd characteristic. Let W+W be contained in S,
and let R be any forbidden finite set of scalars. If

    2 (|R||W| + |S|) < |K|,

one translate V=a+W is disjoint from R, has no opposite parameter pair,
and has quadratic-character convolution L1 norm E satisfying

    E^2 <= 8 |S| |W|^2.

The forbidden translations are exactly the union of R-W and -(S)/2.
Their cardinality bound and the averaged character-energy estimate give
the result. The energy constant does not grow with the forbidden set.

For disjoint parameter sets U,V, the new union inequality is

    L1char(U union V) <= L1char(U)+L1char(V)+2|U||V|.

This explicitly retains the mixed cost instead of assuming that separately
flat sets have flat mixed counts.

## 2. Growing parameters and exact old membership

For an odd-degree extension F -> K, take R to be the whole embedded F.
Adjoin the selected fresh V to the embedded old parameter set U. Then:

* the new parameter cardinality is |U|+|W|;
* the old scalar slice of the parameter set is exactly U;
* nonzero/no-opposite conditions are preserved;
* the actual parabola union has exactly the old field-plane slice;
* its character budget is at most

      oldCharacterBudget + E + 2|U||W|.

The old character budget is preserved by the existing odd-extension
identity. This is a genuinely growing parameter set, not the earlier
unchanged-label extension.

## 3. Growing origin repair

A prescribed old repair set T can be enlarged to a scalar set Q of any
cardinality m satisfying

    |T| <= m,
    m-|T| <= |K|-|F|,

while preserving its exact old scalar slice. The corresponding partial
curve and its symmetric origin repair consequently preserve their exact
old field-plane slices as well.

Take m=floor((|U|+|W|)^2/2). For the ACTUAL repaired set B the origin count is
exactly 1+2m, hence within one of the new nominal mean (|U|+|W|)^2.
At every target, including zero, the absolute error is at most

    oldCharacterBudget + E + 2|U||W| + 10(|U|+|W|)+9.

The old repair curve parameter must be nonzero and unused, with its
negative unused as well. These hypotheses are retained explicitly.

## 4. No small-doubling input needed for the subfield specialization

Let q=|F|>=3 and |K|>=q^3. Use W=S=the embedded old field. All size and
repair-capacity inequalities above then follow automatically, since
|U|,|T|<=q.

The new mean is (|U|+q)^2. The all-target error bound is

    |U|^2 + E + 2|U|q + 10(|U|+q)+9,    E^2<=8q^3.

`exists_accurate_subfield_block_extension` gives relative error at most
 epsilon, simultaneously at all field-plane targets, under

    0<epsilon<=1,
    10|U|<=epsilon q,
    1600<=epsilon^2 q.

The same actual set has the exact old repaired field-plane slice.

## What remains missing

This removes the absence of a growing-label, finite-field error estimate
under the displayed extension hypotheses. It does not establish the
original conjecture:

* No ordinary integer carry estimate follows from the field-plane counts.
* Exact old field-plane membership is not an assertion that field-group
  representations at old targets use only old endpoints.
* The new mean has not been tuned to a fixed coefficient times the
  logarithm of an ordinary natural scale.
* All intermediate natural prefixes between field scales remain uncontrolled.
* No infinite family with the original natural-number limit is claimed.

The collective-repair review preceding this construction supplied no new
incidence bound or coordinated natural-number repair. It must not be used
as an additional assumption.

## Subsequent fixed-coefficient logarithmic tuning

`LogTunedFieldExtensionProgress.md` records a checked construction of actual
odd extension fields and a fixed-coefficient estimate normalized by
log(|K|^2), with an exact old field-plane slice. Thus the finite-field tuning
limitation above has now been removed under the stated hypotheses. Ordinary
integer carry transfer and intermediate natural prefixes remain unproved.
