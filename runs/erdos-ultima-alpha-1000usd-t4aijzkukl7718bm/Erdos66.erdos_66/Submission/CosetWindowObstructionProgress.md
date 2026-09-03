# Natural doubling-window obstruction for coset-block field encodings

## Original task status

The original conjecture remains unproved and undisproved. `Submission/Spec.lean`
is unchanged, with its original `sorry`. No proof or disproof was submitted.
The nonexistence statements below have additional encoding/thin-window
hypotheses and are NOT the negation of the original conjecture.

## Verified production files

* AffineOldPlaneSliceExplore.lean
* SquareAnnulusMassExplore.lean
* CosetWindowObstructionExplore.lean

All three compile with current oleans and no warnings. The 16 declarations
in `CosetWindowObstructionAudit.lean` use only `propext`, `Classical.choice`,
and `Quot.sound`; the saved audit log records this. No production placeholder
or new axiom was added.

## Off-plane affine slices

For an odd-characteristic finite field K, a subfield k, a nonzero parameter
u, and z outside k^2,

    r_(curve(u),oldPlane(k))(z) <= 2.

The proof reuses the already verified three-old-values argument from
`FreshCurvePrefixExplore`: because the target is outside the old plane,
removing a curve's old-plane part does not change the relevant pair count.

Summing over parameters and covering the partial origin repair by curves
w and -w gives, for every repair subset T and w!=0,

    r_(parabolaSet(U) union repairPoints(w,T),oldPlane(k))(z)
      <= 2|U|+4.

This counts the ACTUAL points in an affine old-plane coset. There is no
assumption about avoiding opposite parameter pairs or the size of T.
Every parameter in U must be nonzero.

## Exact natural-window consequence

Let e be injective on [N,2N). Suppose its image on that window is contained
in one affine old-plane coset outside the old plane, and natural membership
in A agrees there with membership in the repaired parabola model. Then

    count(A,2N) <= count(A,N)+2|U|+4.

The proof injects the exact cutoff difference into the finite coset slice.
No field-group representation count is identified with an integer sum count.
The encoder is only required to be injective on the finite window; an
impossible global injection from Nat into a finite field is NOT assumed.

In the subfield-block parameter regime |U|<=2q and N=q^2, this gives

    count(A,2q^2) <= count(A,q^2)+4q+4.

## Universal necessary annular mass for a witness

The verified counting profile and doubling-ratio limit imply, for ANY
hypothetical witness and every fixed real C, eventually q,

    count(A,q^2)+Cq+C < count(A,2q^2).

The proof uses q/count(A,q^2)->0 and
count(A,2q^2)/count(A,q^2)->sqrt(2)>5/4.

Thus infinitely many thin windows with a fixed linear bound exclude the
logarithmic limit. The encoding endpoint allows the field, subfield,
encoder, parameter set, and repair set to vary with q, and arbitrary
ordering WITHIN the displayed coset. It still assumes the whole next
window lies in one off-old-plane coset and the parameter count is <=2q.

The stronger necessary-budget endpoint says that, for each fixed C,
eventually ANY such coset encoding of a witness's [q^2,2q^2) window must
have

    |U| > Cq.

No contradiction is inferred when the parameter count is allowed to grow
superlinearly in q.

## Consequence for the recently constructed finite-field models

The actual subfield-block constructions use a repaired parabola model with
new parameter cardinality |U_old|+q<=2q. Therefore a plain coset-by-coset
natural encoding of these models has the thin-window problem above. This
is a mass obstruction, not merely an unoptimized carry-error constant.

It does NOT rule out interleaving many cosets within a window, using more
parameters, choosing different finite models, or an unrelated construction.
The generic fresh-block lemma permits larger blocks, but their natural
prefix counts and carries have not been controlled here. No unrestricted
proof or disproof of Spec.lean follows.
