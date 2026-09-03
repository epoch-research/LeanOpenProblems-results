# Shared-point repair templates

## Status

The original conjecture is still unresolved. Spec.lean is unchanged and no
completed proof has been submitted. This continuation checks identities and
constraints for a point-reusing alternative to disjoint packets.

## A reusable cross-profile (checked)

`ReusableSidonTemplateExplore.lean`, namespace
`Erdos66ReusableSidonTemplate`, defines

    shift(t,U) = t+U,
    reusable(U,V,t) = (t+U) union (-t+V).

Assuming the shifted halves are disjoint, the exact identity is

    r_reusable(z) = r_U(z-2t) + 2 pairs(U,V,z) + r_V(z+2t).

Thus the ENTIRE cross profile is preserved as t varies, with |U|+|V|
vertices serving all its targets. If U,V are Sidon, then

    2 pairs(U,V,z) <= r_reusable(z) <= 2 pairs(U,V,z)+4

at every target. This is a genuine way to reuse points, but it requires
an appropriate prescribed mixed profile pairs(U,V), not an arbitrary list
of separately chosen centers.

If both U and V have uniformly at most R mixed representations with an old
finite A, and the inserted set is disjoint from A, the checked union bound is

    r_A(z)+2 pairs(U,V,z) <= r_(A union reusable)(z)
      <= r_A(z)+2 pairs(U,V,z)+4R+4.

This is conditional on template compatibility with A. It does not construct
compatible U,V for the actual exceptional targets.

## Translation does not solve compatibility (checked)

For fixed U and old A,

    pairs(t+U,A,z) = pairs(U,A,z-t).

Consequently a uniform bound over ALL integer targets is equivalent before
and after translation. Any old/template mixed peak persists, at a shifted
target, in the whole reusable set. Opposite translation alone cannot select
away all the old/template mixed peaks. This formalizes the diagnostic
already noted in TemplatePacketProgress.md.

## Shared-endpoint rigidity (checked)

`SharedEndpointRigidityExplore.lean`, namespace
`Erdos66SharedEndpointRigidity`, considers two vertex labelings x,y of a
graph giving the same prescribed sum on each edge. Along a walk of length l,

    y(v)-x(v) = (-1)^l (y(u)-x(u)).

An odd closed walk forces zero displacement throughout its reachable
component. For a connected bipartite graph, all realizations differ by only
one parameter: +t on one side and -t on the other.

For a complete bipartite template with prescribed center matrix n(i,j),
realizability is equivalent to

    n(i,j)+n(i0,j0) = n(i,j0)+n(i0,j)

for every i,j. All realizations then have the explicit one-parameter form
proved in `rectangle_parameterization`. One cannot retain independent
sampling variables for every edge after identifying their endpoints.

## Sidon reuse budget (checked)

`ReusableSidonEnergyExplore.lean`, namespace
`Erdos66ReusableSidonEnergy`, proves that when V is Sidon,

    sum_(z in T) pairs(U,V,z)(pairs(U,V,z)-1) <= |U|(|U|-1).

Two distinct U vertices can participate together at only one common target:
otherwise V has a nontrivial repeated sum. Their off-diagonal pair sets
are therefore disjoint across targets. Applying the same argument with
U,V reversed gives the two-sided bound.

If U,V are Sidon and pairs(U,V,z)>=k on T, then

    |T| k(k-1) <= min(|U|(|U|-1), |V|(|V|-1)),
    |reusable| >= 2 sqrt(|T| k(k-1)).

This resource bound is different from disjoint-packet cost |T|k and does
not exclude reuse at power-sparse target families. It also does not assert
existence of a template attaining the bound for an arbitrary target set.

## Remaining gap

No reusable template was constructed with BOTH the required defect profile
and uniformly negligible mixed counts with a suitable old base. Cardinality
bounds on the exceptional set alone supply neither property. The rigid
shared-sum constraints and translation identity cannot be discarded in a
joint sampling argument.

The review did not yield a replacement infinite construction, a compatible
change-of-modulus argument, or a universal obstruction. Nothing here proves
or negates the existential statement in Spec.lean.

## Verification

All three production files compile and have current oleans. Main theorems
are audited in ReusableTemplateAxiomCheck.lean, using only propext,
Classical.choice, and Quot.sound. The files contain no placeholders or new
axioms. Name-search scratch check files are not production dependencies.
