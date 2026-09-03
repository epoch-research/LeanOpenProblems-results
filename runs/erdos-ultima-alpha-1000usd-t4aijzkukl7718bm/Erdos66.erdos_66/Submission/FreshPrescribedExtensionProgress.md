# Fresh curves and arbitrary prescribed old sets

## Original task status

The conjecture remains unproved and undisproved. Spec.lean is unchanged,
including its original import, statement, and sorry. No proof has been
submitted. The results here are auxiliary finite-field results and a
necessary natural-number transition condition, not a solution.

## Verified production files

* FreshCurvePrefixExplore.lean
* FreshOddExtensionExplore.lean
* PrescribedOddFieldExtensionExplore.lean
* CosetPrescribedExtensionExplore.lean
* NaturalBoundaryMixedExplore.lean

All five compile and have current oleans. FreshPrescribedExtensionAudit.lean
checks 28 declarations. Its log uses only propext, Classical.choice, and
Quot.sound. FreshExtensionChecks.lean and BoundaryChecks.lean are scratch
API searches, not production dependencies.

## 1. Arbitrary old plane versus fresh curves

Let k be a subfield of an odd-characteristic finite field E and let
P=k x k. A is ANY subset of P, chosen before all new curves. For u != 0
put

    C_u = {(x,x^2/u): x in E},    C_u^fresh = C_u \ P.

The checked theorem gives, for every target z,

    r_(A,C_u^fresh)(z) <= 2.

There is no dependence on |A|, and u need not belong to k. The proof shows
that a translated quadratic taking old-field values at three distinct
old-field inputs must have all its coefficients in the old field. Thus
the three allegedly fresh endpoints would actually lie in P.

For B supported on h fresh curves, r_(A,B) <= 2h, (A union B) intersect P=A,
and A,B are disjoint. If B is flat at a target about mu with error err and
r_A at that target is bounded by g, then

    |r_(A union B)-mu| <= err+4h+g.

The retained old self-count cost g is explicit in this general statement.

## 2. Stronger square-closed extension: exact old counts

Suppose k is square-closed in E: x^2 in k implies x in k. For an old
parameter set U subset k excluding zero and opposite pairs, put

    C=union_(u in U) C_u,    B=C \ P,    A_new=A union B.

A completed-square calculation shows that two curve endpoints with old
sum must themselves be old. Consequently, for EVERY old target z in P,

    r_B(z)=0,    r_(A,B)(z)=0,    r_(A_new)(z)=r_A(z).

This includes the origin; no origin repair is needed. The no-opposite
parameter condition is essential.

For z outside P, both r_A(z) and r_(C intersect P)(z) are zero. Comparing
the two exact disjoint-union identities, and using the mixed caps, gives

    |r_(A_new)(z)-r_C(z)| <= 4|U|.

Combining with the actual parabola-set character estimate gives

    |r_(A_new)(z)-|U|^2|
      <= sum_w |charFiber(U,w)| + 6|U|.

There is NO old-cardinality or old-self-cap term at new targets. This is
stronger than the initial conditional E+4h+g bound.

## 3. Actual odd-degree extension endpoint

For finite fields F -> E with odd degree, square-closure and character
preservation are already established in the earlier odd-extension work.
The new theorem exists_prescribed_extension uses these to prove:

    for arbitrary A subset F^2 and arbitrary nonempty admissible U subset F,
    there is B subset E^2 such that
      membership on the embedded F^2 is exactly A;
      every embedded old representation count is exactly r_A;
      all targets outside embedded F^2 have the preceding flatness bound,
      with the character budget computed in F, not E.

Unlike the earlier fixed-template extension, A need not be a parabola
union or belong to a palette selected in advance. U may be chosen after A.
The full theorem is in PrescribedOddFieldExtensionExplore.lean.

## 4. Coset instantiation

If K -> F is quadratic and F -> E has odd degree, with q=|K| and odd
characteristic, a translated quadratic coset U in F has |U|=q and

    err=sum_w |charFiber(U,w)|,    err^2 <= 3q^3.

For ANY prescribed old A subset F^2, the checked endpoint supplies B with
exact old membership and exact old counts, and for every new target

    |r_B(z)-q^2| <= err+6q.

This is an actual finite-set construction, not merely an assumed flat
kernel. Properness of the final extension is not required by the statement;
if its degree is one the new-target assertion is vacuous. No natural-number
ordering or intermediate-scale density is asserted.

## 5. Natural boundary condition: small mixed error is not a transition mean

For A subset N, define

    boundaryMixed(A,M)=#{a<M: a in A and 2M-1-a in A}.

For M>0 the exact checked identity is

    sumRep(A,2M-1)=2 boundaryMixed(A,M).

Both endpoints below M sum to at most 2M-2, while both endpoints at least
M sum to at least 2M. Thus every representation of 2M-1 is old/new.

If A were a witness with coefficient c, then

    boundaryMixed(A,M)/log(2M-1) -> c/2.

Since c>0, at NO unbounded sequence of cutoffs can these mixed counts have
an eventual sublogarithmic cap. In particular, an eventual bound

    boundaryMixed(A,M_j) <= C sqrt(log(2M_j-1))

is impossible for every fixed C and M_j -> infinity.

This diagnoses a limitation of a direct transfer of the fresh-curve cap
2h when h^2=O(log M) at the transition scale. It is NOT an obstruction to
all density-changing constructions. If h^2 is tuned instead to a much
larger future logarithm, the displayed root-log cap at M need not hold;
the intermediate-scale and changing-density problems then still need to
be solved. Nor does any theorem here force arbitrary natural sets to
satisfy the fresh-curve mixed cap.

## Missing main step

There is still no compatible natural-number construction through all
intermediate scales, no ordinary-carry transfer for these arbitrary-old-set
extensions, and no universal contradiction from the witness hypothesis.
Finite-field flatness, exact old-plane count preservation, and small mixed
caps do not supply the necessary natural transition means. Spec.lean must
not be replaced by any of these partial theorems.
