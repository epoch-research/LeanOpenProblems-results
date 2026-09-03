# Intercept parabolas: literal first row and exact collision correction

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original import, statement, and sorry. This is an auxiliary
finite-field investigation, not a solution or a disproof.

## Construction and complete root formula

For nonzero field labels u define the curve

    P_u(k)=(u+k^2/u,k).

The union B(U) has row zero exactly U, without removing a common origin.
After translating the parameters by a and undoing the horizontal shift,
row zero is exactly the original U. The ordinary radix encoding therefore
preserves every old membership bit and sumRep count below the prime p.

For nonzero u,v with u+v nonzero, its ordered parameter-root count is

    1+chi(u)chi(v)chi((u+v)(t-u-v)-q^2).

Thus the weighted complete count W(U,V;q,t) has exactly the usual mixed
character-fiber formula, with the target factor chi(s(t-s)-q^2). If U,V
have no opposite pairs, uniformly over all targets,

    |W-|U||V|| <= sum_s |crossCharFiber(U,V;s)|.

This statement is about counts WITH PARAMETER MULTIPLICITY.

## Actual curves do intersect

For distinct nonzero u,v,

    P_u(k)=P_v(k) iff k^2=u*v.

There are no triple intersections. Let D(U) be the set of double-covered
points. The exact multiplicity is 1_B+1_D, and hence

    W(U,U;z)=r_B(z)+2 r_(B,D)(z)+r_D(z).

The correction is nonnegative but is not automatically negligible.
A kernel-checked example over F_7 with U={1,2} has

    W(U,U;0,6)=8,    r_B((6,0))=2.

Thus equality of weighted and actual counts is genuinely false even at a
nonzero target with no opposite parameters.

## Exact mass identities

Put h=|U| and S=sum_(u in U) chi(u). Pairwise curve intersections and the
absence of triple intersections give

    2|D|=h^2-2h+S^2,
    |B|+|D|=p h,
    |D|<=h^2.

The generic TwofoldFamilyExplore.lean proves the same multiplicity,
convolution and mass corrections for arbitrary finite families with
multiplicity at most two; no field geometry is assumed in that file.

## What survives for the actual set

Write deficit(z)=W(z)-r_B(z). It is nonnegative, and

    sum_z deficit(z)=2|B||D|+|D|^2 <=2p h^3.

If |W(z)-h^2|<=E everywhere, then

    r_B(z)<=h^2+E                        for every z,
    sum_z |r_B(z)-h^2|<=p^2 E+2p h^3.

These are an actual pointwise UPPER bound and an L1 error bound. They are
not a pointwise lower bound. In particular, small total collision mass
cannot be silently upgraded to a uniform o(h^2) correction.

## Sources and remaining issue

Production files:

* TwofoldFamilyExplore.lean
* InterceptCurveExplore.lean
* InterceptCollisionCorrectionExplore.lean
* InterceptUpperAndMassExplore.lean
* InterceptPrefixExplore.lean
* InterceptCollisionExampleExplore.lean

Build and axiom checks are recorded in InterceptCurveBuild.log and
InterceptCurveAudit.lean/.log. The six sources contain no sorries or new
axioms; the concrete finite example uses kernel evaluation, not native
unchecked computation.

The construction does not yet control the spatially restricted roots in
short transition windows, supply the required tapered natural counts, or
compare successive moduli. It also retains the need for a pointwise
collision bound if its weighted lower estimates are to be used. The prior
faithful-lift construction already has exact row-zero preservation and
complete set-level estimates by a different geometry; the new graph model
must not be presented as resolving that older transition gap.

The review of common-source density retuning and color-dependent phases
has not produced a compatibility lemma. No cutoff-independent finite
feasibility theorem or infinite witness has been obtained.

## Subsequent pointwise correction theorem

GoodInterceptProgress.md records a proved general-position selection. If
2(8|U|^7+|U|^2)<|F|, one translation has pointwise collision correction at
most 12|U|, simultaneously at every target, while retaining low character
energy and the exact old first row. Thus the pointwise collision gap is
closed under that explicit condition. A separate checked density argument
shows that this sufficient condition eventually fails for full prefixes
of a hypothetical witness; the scale-transition gap remains unresolved.
