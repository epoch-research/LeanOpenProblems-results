# Non-Cartesian quadratic field lift: stable curve cap, unstable union flatness

## Original task status

The conjecture in Submission/Spec.lean remains unresolved. Its original
import, statement, and sorry are unchanged. No proof or disproof has been
submitted. The finite results here do not settle the existential natural
number statement.

## Production files and verification

* QuadraticFieldLiftExplore.lean
* QuadraticExtensionCharacterExplore.lean
* QuadraticLiftUnionExplore.lean

All three compile with current oleans. QuadraticFieldLiftAudit.lean audits
22 declarations; its saved log contains only propext, Classical.choice,
and Quot.sound. There are no production sorries, admits, or new axioms.
A few harmless unused-section-variable warnings remain.

QuadraticExtensionChecks.lean and OddExtensionChecks.lean are API scratch
files with intentionally unsuccessful searches, not dependencies.

## 1. A genuine non-Cartesian lift

Let F be a finite field, d a nonsquare, and

    E=QuadraticAlgebra F d 0.

The existing Mathlib quadratic algebra becomes a field because r^2=d has
no solution. The new file checks |E|=|F|^2 and equality of characteristics.
It uses the additive coordinate equivalence

    ((r,y),(x,z)) <-> (r+x sqrt(d), y+z sqrt(d)).

For u!=0, the lifted curve has exact membership

    y=(r^2+d*x^2)/u,
    z=2*r*x/u.

Thus the old coordinate changes with the new row, and the new high output
also depends on the old input. This is not a full affine-line lift with
unchanged old points, nor a Cartesian product of two old curves.

At x=z=0 its membership is exactly the old parabola y=r^2/u.
Each lifted curve has |F|^2 points. If the characteristic is not two and
u,v,u+v are nonzero, ALL mixed counts of the two lifted curves are at most
TWO, including the origin. The cap does not multiply on this step: these
are single parabolas over the larger field E. Their individual global
convolution means are exactly one.

This is a stable algebraic curve class, not a growing logarithmic profile.
No natural prefix or intermediate-scale density conclusion is drawn from
its old-plane membership assertion.

## 2. Quadratic extensions erase old quadratic characters

QuadraticExtensionCharacterExplore proves directly that every old scalar
maps to a square in E. If u is an old square this is immediate. Otherwise
u/d is an old square, since both u and d have quadratic character -1, and
its square root times sqrt(d) supplies a root of u in E.

Consequently every nonzero old scalar has quadratic character +1 in E.
A previously good old character pattern is therefore not preserved.

## 3. Exact holes and double counts for inherited unions

The more general lemmas use any field embedding j:F->E whose entire image
consists of squares. For arbitrary parameter sets U,V and ANY nonsquare
s in E,

    r_(parabolaSet(jU),parabolaSet(jV))(0,s)=0.

No nonzero-label, no-opposite, or nonemptiness hypothesis is needed for the
hole theorem. A hypothetical representation would imply

    s=x^2*j(u^-1+v^-1),

which is a square.

If U,V are nonempty, all labels are nonzero, and no u+v vanishes, then

    r_(parabolaSet(jU),parabolaSet(jV))(0,1)=2|U||V|.

Each parameter pair gives two roots. At (0,1) the graph indicators vanish,
so the common-origin multiplicity correction is zero: this is an exact
count for the ACTUAL sets, not a weighted surrogate.

## 4. The same facts in the four-coordinate lift

Define liftUnion(U) as the union of the actual lifted curves. It is exactly
the additive image of parabolaSet(jU), and its old zero-slice membership is
exactly parabolaSet(U) when all old labels are nonzero.

A nonsquare of E cannot have zero imaginary coordinate, since all old
scalars became squares. The hole can therefore be chosen OFF the retained
old plane.

The target corresponding to (0,1) is the OLD-plane target ((0,1),(0,0)).
Its new count is exactly 2|U||V|. This is twice the nominal parameter-pair
mean, not a claim that it is twice the actual old count. It demonstrates
why old-slice membership alone does not preserve group representation
counts: new coordinates can cancel.

For nonempty U,V, the inherited unions cannot be uniformly relatively
accurate about |U||V| with any tolerance epsilon<1. This last statement is
about the specified unchanged-label union and nominal mean, not every
possible enlargement or a density-adjusted logarithmic construction.

## 5. What was not re-proved or obtained

The earlier odd-degree extension results were rechecked, not re-proved.
CharacterNormExplore, OddFieldExtensionExplore,
OddExtensionCharacterFiberExplore, and OddExtensionFlatSetExplore already
preserve old square classes, signed-fiber budgets, and suitable repaired
old slices under odd extensions. See OddExtensionProgress.md.

Those results keep the same old parameter set and mean. They still do not
construct a growing family of labels with the required error, or an
inhomogeneous natural set with compatible all-scale prefix counts.

The new quadratic-field calculation shows that avoiding the full-line
peak obstruction and retaining a joint cap are not by themselves enough
to retain union flatness. It does NOT rule out fresh parameters, deletion
or replacement of inherited points, other point-dependent maps, or an
unrelated infinite construction. No group peak or hole here is asserted
to transfer through arbitrary ordinary integer carries.

There remains no compatible natural-number witness, cutoff-independent
finite-prefix feasibility proof, pointwise sublogarithmic quadratic
Boolean rounding, or universal contradiction settling Spec.lean.
