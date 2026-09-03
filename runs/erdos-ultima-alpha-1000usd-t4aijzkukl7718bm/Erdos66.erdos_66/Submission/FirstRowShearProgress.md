# First-row-fixing shears and exact ordinary carry averages

## Original conjecture

The conjecture in Spec.lean is still unproved and undisproved. Its statement,
import, and original sorry are unchanged. No proof has been submitted.

## Verification

* FirstRowFixingShearExplore.lean
* RowShearNaturalAverageExplore.lean

Both compile without warnings and have current oleans. FirstRowShearAudit.lean
audits nineteen declarations; the saved log uses only propext, Classical.choice,
and Quot.sound. Neither production file contains sorry or a new axiom.

## Preserved row and complete counts

The additive equivalence H_b(x,y)=(x+b*y,y) fixes every point of row zero.
For arbitrary finite plane sets B,C,

    r_(H_b B,H_b C)(t,s) = r_(B,C)(t-b*s,s).

Thus an all-low-target error bound in one horizontal slice is equivalent
before and after shearing. A common shear cannot improve that uniform
complete-count bound; it only permutes the targets.

## Exact weighted spatial average

For finite row sets A,B over a finite field, row heights y,v with y+v!=0,
and any real spatial weight w, define

    weightedPair(A,B;t,w)=sum_(a in A,c in B,a+c=t) w(a).

The checked identity is

    sum_b weightedPair(b*y+A,b*v+B;t,w)
      = sum_(a in A,c in B) w((v*a-y*c+y*t)/(y+v)).

With w=1 the right side is |A||B|. With an interval indicator, however,
the linear combination remains inside the interval condition. A spatially
restricted root count has NOT been replaced by a proportion of the full
count.

For the retained first row y=0 and v!=0 this simplifies to

    sum_b weightedPair(A,b*v+B;t,w) = |B| sum_(a in A) w(a).

Consequently the lower-carry average depends on the ACTUAL old prefix mass.

## Actual first natural transition window

For prime p, place A in row zero and b+B in row one, with other rows empty.
Let S_b be the resulting natural block set. All old bits below p agree with A.
For 0<=t<p, the exact count is

    r_(S_b)(p+t)=2 lower(A,b+B;t)+upper(A,A;t).

Averaging over all p phases gives

    sum_b r_(S_b)(p+t)
      = 2 |B| #{a in A : a.val<=t} + p upper(A,A;t).

Equivalently, the mean is

    (2|B|/p) #{a in A : a.val<=t} + upper(A,A;t).

This is an ordinary natural-number identity with both carry terms retained,
not a cyclic or product-group surrogate. In particular, a uniform phase
average is not automatically the desired constant logarithmic mean in the
first transition window.

## What remains missing

The formula is an average, not a simultaneous choice of one phase for all
natural targets. Neither a sublogarithmic bound for the weighted residual
kernel nor a compatible changing-scale construction has been proved. The
existing tapered-row membership formula and complete character-fiber bounds
do not, by themselves, supply those estimates. No universal contradiction
to the original existential statement follows from these identities.

External reference access was checked again; both DNS-based access and direct
IP HTTPS connections were unavailable. No new external result was used.

## Centered-energy estimate for the spatial residual

Two further production files now compile without warnings and have current
oleans:

* WeightedShearEnergyExplore.lean
* NaturalShearEnergyAverageExplore.lean

WeightedShearEnergyAudit.lean audits ten further declarations. The saved log
uses only the permitted axioms.

Suppose the complete cyclic self-counts of A and B have uniform errors E,D
about arbitrary centers. For any real weight w, the centered mixed-energy
inequality and Cauchy--Schwarz give

    [sum_(a in A,b in B) w(a+b) - (|A||B|/q) sum_z w(z)]^2
      <= [sum_z w(z)^2] q E D,

where q is the group cardinality. Self-count errors are preserved under
additive automorphisms, including nonzero field dilations.

For nonzero row heights y,v with y+v!=0, the exact weighted shear average
can be rewritten as such a mixed convolution of two invertible dilations.
Thus the SAME bound holds for its error from the uniform spatial mean.
If 0<=w<=1, division by q gives

    |averaged weighted count - (|A||B|/q^2) sum_z w(z)|^2 <= E D.

For the actual lower carry in ZMod p, 0<=t<p, this specializes to

    |(1/p) sum_c lower(c*y+A,c*v+B;t)
          - |A||B|(t+1)/p^2|^2 <= E D.

The bound is uniform in the target and both nonzero row heights. The zero
row is deliberately excluded here: its exact first-row formula above,
which depends on the old prefix mass, still applies separately.

If one self-error is O(log p) and the other is o(log p), the displayed
error of the AVERAGE is o(log p). This is a genuine spatial averaged-count
estimate, not merely an unweighted complete-root identity. It still does
not choose one shear for all targets or prove a compatible infinite chain.
