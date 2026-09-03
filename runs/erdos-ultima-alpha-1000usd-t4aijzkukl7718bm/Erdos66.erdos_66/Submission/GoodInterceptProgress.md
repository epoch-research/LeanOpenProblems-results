# Generic translations give pointwise collision control

## Original conjecture status

Erdos66.erdos_66 is still unproved and undisproved. Spec.lean remains
unchanged, including its original import, statement, and sorry. These are
finite-field results and a check of their scope, not an infinite witness.

## New finite endpoint

For an odd finite field F, write p=|F|, h=|U|, and suppose all parameter sums
u+v belong to a finite S. Under the EXPLICIT sufficient field-size condition

    2(8h^7+h^2)<p,

exists_good_anchored_graph selects a translation a for which the actual
anchored intercept-curve union B has

    (x,0) in B iff x in U,
    |r_B(z)-h^2| <= sqrt(8 |S| h^2)+12h    for EVERY field-plane target z.

There is no exceptional target in this endpoint. The earlier ordinary
encoding lemma gives literal membership and representation preservation
below p. It does not turn the displayed complete field-plane estimates
into ordinary estimates above p.

## The collision gap is now closed in this regime

The preceding intercept development established only a pointwise upper
bound and a total-error estimate because curves can collide. The present
work proves the needed pointwise correction for a selected translation:

    |r_B(z)-W(z)| <=12h.

Here W is the root count with parameter multiplicities. Its character-fiber
estimate is combined with the exact identity

    W=r_B+2r_(B,D)+r_D,

where D is the collision set. This is no longer an average or an assumed
pointwise bound. The field-size condition above is essential to the proved
selection argument and is retained throughout.

## Polynomial general-position argument

A collision between the shifted labels a+u and a+v has coordinates

    x=2a+u+v,    k^2=(a+u)(a+v).

If three collision pairs lie on one reflected curve with label a+w,
eliminating the target coordinates gives a linear relation among the three
square roots. Eliminating those roots gives a polynomial in a of degree
at most eight.

For two distinct unordered pairs, the product of their quadratic
polynomials has a simple root. The root multiplicity of a square is even,
so that product cannot be a square times a rational square. This proves
that the elimination polynomial is NONZERO; a formal degree bound alone
would not suffice.

There are at most h choices of w and h^6 ordered triples of pairs. Their
root sets therefore have total union cardinality at most 8h^7. A further
h^2 forbidden values exclude zero labels and opposite pairs. The existing
energy selector chooses a outside their union while retaining signed
character energy at most 8h^2.

At that translation, any reflected curve meets collision points from at
most two unordered label pairs. Each pair has at most two square roots,
so its collision count is at most four. Summing over h curves gives

    r_(D,B)(z)<=4h,    r_D(z)<=4h,

and hence the correction bound 12h. This holds simultaneously at every
target, for one chosen translation.

## Checked scope restriction

The density required by a hypothetical witness gives

    count(A,N)^2/(N log N) ->4c/pi >0.

InterceptSelectionScaleExplore.lean derives

    eventually N<count(A,N)^2.

Consequently the selector's sufficient inequality

    2(8 count(A,N)^7+count(A,N)^2)<N

eventually FAILS for every full old prefix, including actual modular
prefixParameters(A,p) at sufficiently large prime p.

This is only a failure of that sufficient certificate. It does not rule
out other translations, other selection bounds, or witnesses to the
original conjecture. It does show why the new finite theorem cannot be
silently iterated on full prefixes at the required density.

## Files and verification

Six production files compile without warnings:

* InterceptEdgePolynomialExplore.lean
* InterceptConcurrencyPolynomialExplore.lean
* InterceptGoodTranslationExplore.lean
* InterceptCollisionIncidenceExplore.lean
* GoodInterceptFlatExplore.lean
* InterceptSelectionScaleExplore.lean

GoodInterceptBuild.log records the rebuild. GoodInterceptAudit.lean/.log
checks 66 declarations; only propext, Classical.choice, and Quot.sound
occur. None of these production files
contains a placeholder or a new axiom.

The remaining infinite issue is still a density-compatible construction
controlling all natural transition windows. Neither complete field-plane
flatness nor the exact first-row identity supplies it.
