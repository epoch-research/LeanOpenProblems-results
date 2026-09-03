# Concrete line recoloring and an obstruction to literal fixed-field iteration

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged,
with its original import, statement, and sorry. No proof was submitted.
SHA256:

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## Verified production files

* GraphRowAssemblyExplore.lean
* LineRecoloringExplore.lean
* OriginLineLiftExplore.lean
* LineRecoloringPeaksExplore.lean
* LineRecoloringIterationExplore.lean

All five compile and have current oleans. LineRecoloringAudit.lean audits
20 principal declarations; LineRecoloringAudit.log reports only propext,
Classical.choice, and Quot.sound. There are no production sorries or axioms.
RecolorLineChecks.lean and LineIterationChecks.lean are API scratch files
with intentionally failed checks.

## 1. Exact graph-row mixed count

For old fibers B_x in a finite additive group G, and a graph f over a finite
field F, assemble

    rowAssembly(B,f) = union_x B_x x {(x,f(x))}.

The graph's first coordinate makes the rows disjoint even when the B_x
are not disjoint. The exact mixed count at (z,(s,t)) is

    sum_{x: f(x)+h(s-x)=t} r_(B_x,C_(s-x))(z).

Thus a root cap D and old joint mixed cap g give new mixed cap Dg. This is
an actual finite-set count, not a formal weighted surrogate.

## 2. Recoloring the tau-line lift

Start from lines (x,u*x+tau*u^2). Assign new color

    v = u + alpha*x.

Then the old color is u=v-alpha*x, and the high-coordinate graph for new
color v is

    f_v(x)=(v-alpha*x)*x+tau*(v-alpha*x)^2.

For two new colors v,w the equation f_v(x)+f_w(s-x)=t is quadratic in x,
with leading coefficient 2*alpha*(tau*alpha-1). In odd characteristic,
if alpha is nonzero and tau*alpha != 1, it has at most two roots.

Consequently the concrete recolored family has ALL mixed counts at most
2g when ALL old mixed counts are at most g. Same-color caps alone are NOT
substituted for the joint old hypothesis.

For disjoint old colors, the new colors are disjoint. Each new color has
cardinality equal to the total old cardinality. Their union is exactly the
original tau-line lift, independent of alpha.

For tau=0, each old color is retained exactly on the zero slice:

    (a,(0,0)) in newColor_v iff a in oldColor_v.

For tau=1 this specializes to a recoloring of the previously constructed
affine-line lift (with alpha != 0,1). Thus the earlier review's missing
one-step joint-cap regeneration is now proved, but with a factor of two.

## 3. Through-origin lift: exact error and origin effect

For tau=0, distinct lines give mixed count one everywhere. A same-color
line gives q=|F| counts when y=u*x, and zero otherwise. For a nonzero high
target (x,y), at most one slope u contributes.

If every old same-color count at z is at most g, then

    |r_lift(z,(x,y))-r_old(z)| <= q*g,     (x,y) != (0,0).

At the high origin the exact formula is instead

    r_lift(z,(0,0))
      = r_old(z)+(q-1) sum_u r_(oldColor_u)(z).

The global mean remains exactly unchanged because cardinality is multiplied
by q and ambient group order by q^2. Preserving zero-slice MEMBERSHIP does
not preserve its REPRESENTATION COUNTS in the finite product group.
In particular this is not yet a natural-prefix or carry-transfer theorem.

## 4. Lower bounds show why the literal iteration fails

Write oldRow(alpha,v,u)=(v-u)/alpha and let oldPoint be its point on f_v.
Any old mixed count survives in any prescribed pair of new colors at the
explicit high target obtained by summing the corresponding oldPoints.
If the old labels u,t are distinct, the same count contributes twice to a
new same-color count, because the two ordered orientations are distinct.

Combining these facts:

    every old self-count can be doubled after two recoloring steps,

in every prescribed final color. This lower bound needs only nonzero alpha
at both steps, not odd characteristic, upper caps, disjointness, or flatness.

## 5. Actual recursive spaces and arbitrary additions

LineRecoloringIterationExplore defines

    Space(0)=G, Space(n+1)=Space(n) x (F x F),

with checked additive-group, decidable-equality, and Fintype instances.
The ambient cardinality is |G| q^(2n).

It permits an arbitrary family B_n whose next color contains the entire
recolored old color. Arbitrarily many ADDITIONAL points are allowed at
every stage. For any nonempty initial color, at depth 2k some self-count
is at least 2^k.

The logarithm of the ambient cardinality at depth 2k is

    log|G|+4k log q.

Hence the checked theorem iteration_exceeds_logarithmic_cap proves that
for EVERY fixed real K,C, eventually k the uncolored union at depth 2k
has some target with count strictly greater than

    K+C log|Space(2k)|.

This is stronger than merely noting an exponential upper-bound loss: the
exponential peaks are proved lower bounds. Adding points cannot remove them.

## Scope and remaining directions

This excludes the literal colorwise-containing iteration over one FIXED
finite field. It does not exclude changing fields with nontrivial recoloring,
clipping/removing inherited fibers, or other constructions. No integer carry
transfer is asserted, and no universal statement about every subset of Nat
is inferred. It is not a disproof of Erdős 66.

A possible further review is the interaction of varying field sizes with
inherited full-line peaks; no varying-field iteration obstruction has yet
been formalized here. More importantly, a successful construction would
need to modify the inherited fibers while retaining natural-prefix accuracy
and regenerating useful mixed control. Neither this development nor the
existing rounding/repair results supplies that missing construction.

## Subsequent changing-field result

ChangingFieldLineProgress.md records a checked extension for FULL affine-line
lifts with injective changes of color alphabet and field, plus arbitrary
colorwise additions. A new field-size peak prevents field growth from
outrunning the inherited two-step doubling. This rules out any eventual
logarithmic finite-product-group cap in that model. It does not cover
point-dependent changes of the inherited copies or assert a natural carry
transfer, and it does not settle Spec.lean.
