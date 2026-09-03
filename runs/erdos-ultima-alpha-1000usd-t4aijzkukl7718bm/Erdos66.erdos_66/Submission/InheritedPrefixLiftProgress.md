# Origin inheritance, exact-prefix lifts, and the full-lift mass obstruction

## Original task status

The conjecture remains unproved and undisproved. Submission/Spec.lean is
unchanged, including its original import, statement, and sorry. No valid
proof or disproof has been submitted.

## Verified production files

* ParabolaOriginInheritanceExplore.lean
* ShearedParabolaPrefixExplore.lean
* InheritedOriginLiftExplore.lean
* PrefixFaithfulParabolaLiftExplore.lean
* FaithfulParabolaCardinalityExplore.lean
* QuadraticPrefixMassExplore.lean
* FullFaithfulLiftObstructionExplore.lean

All seven compile with current oleans. InheritedLiftAudit.lean audits 37
lemmas/theorems. InheritedLiftAudit.log reports only propext,
Classical.choice, and Quot.sound. No production sorries or new axioms were
introduced. InheritedLiftChecks.lean is a name-search scratch file, not a
production dependency.

## Exact inherited origin

For nonempty parameter sets U,V excluding zero in an odd finite field F,
q=|F|, let parabolaSet(U) be the union of y=x^2/u for u in U. Then

    r_(parabolaSet(U),parabolaSet(V))(0) = 1+(q-1)r_(U,V)(0).

Opposite parameters are not automatically forbidden: their contribution
at the origin is exactly inherited from the parameter representation
count. The old DegenerateCrossGraphExplore.lean already supplies the
nonzero-target formula with opposite parameters.

## Literal first-row preservation

The additive shear (x,y) -> (x,y-x) makes the first row of the parabola
union equal to U union {0}. If 2|U|<q, a translation a can be selected so
that U+a excludes zero and its signed character self-energy is at most
8|U|^2; opposite parameters are allowed.

Undo the horizontal translation after shearing and remove the translated
common origin. The resulting faithfulLift(U,a) satisfies

    (x,0) in faithfulLift(U,a) iff x in U.

For a prime p and the literal encoding (x,y) -> x.val+p*y.val, membership
at every natural n<p is exactly membership of (n:ZMod p) in U. Natural
representation counts below p are therefore also preserved exactly.
Deleting the origin changes each field-group self-count by at most two.

The nonexceptional field-group estimate is

    |r_new(z)-|U|^2| <= sqrt(8q|U|^2)+3|U|+2.

The exceptional target is retained explicitly after undoing the shear and
translation. If |r_U(t)-mu|<=E at every field target, its estimate is

    |r_new(z)-[1+(q-1)mu]| <= (q-1)E+2.

For mu=|U|^2/q, the nominal new mean is |U|^2=q*mu. It has not been
retuned to the logarithmic scale. Field-group estimates outside the old
prefix are not asserted to be natural-number estimates.

## Exact mass and a necessary obstruction

The punctured graph union is parametrized injectively by U times F\{0}.
Consequently

    |faithfulLift(U,a)| = |U|(q-1).

The natural encoding is injective, with all points below p^2, so its
cardinality for a prime p is |U|(p-1).

Independently, the checked counting-square profile of any hypothetical
witness gives the new necessary condition

    eventually count(A,N^2) < (N-1)count(A,N).

Here count(A,N)=|A intersect [0,N)|. The proof uses the positive limit
count(A,N)^2/(N log N) -> 4c/pi at N and N^2. The reverse inequality
would force (N-1)^2<8N, contradicting sufficiently large N.

Let prefixParameters(A,p) be the image of A intersect [0,p) in ZMod p.
It has exactly count(A,p) parameters. If A contains the ENTIRE encoded
faithful lift of these parameters, then

    count(A,p^2) >= (p-1)count(A,p).

The theorem eventually_no_full_faithful_lift therefore excludes this
containment at every sufficiently large prime p, for every admissible
translation a. No assertion about existence or nonexistence of a witness
is inferred from this construction-specific restriction.

## Remaining gap

Keeping the full lift at unbounded scales has the wrong mass. Thinning it
could change the mass, but neither the field-group flatness estimates nor
the exact-prefix property give the required natural representation counts
after such thinning. There is still no compatible density-adjusted
infinite construction, uniformly sublogarithmic Boolean quadratic
rounding theorem, cutoff-independent finite-prefix feasibility result, or
universal logarithmic-order fluctuation contradiction.
