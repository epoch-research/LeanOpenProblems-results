# Full affine-line iteration with varying finite fields

## Original conjecture status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged,
with its original import, statement, and sorry. No proof was submitted.
The new theorem is a restriction on one construction model, not the
negation of the existential statement in Spec.lean.

## Production files and audit

* ChangingFieldLineStepExplore.lean
* ChangingFieldGrowthExplore.lean
* ChangingFieldIterationExplore.lean
* ChangingFieldLogCapExplore.lean

All four compile with current oleans. ChangingFieldLineAudit.lean audits
24 declarations; the saved log uses only propext, Classical.choice, and
Quot.sound. No production source contains sorry, admit, or a new axiom.
There are a few harmless unused-section-variable and tactic-style warnings.

## 1. The model, including the quantifiers

Let F_n be an arbitrary sequence of finite fields. Old colors F_n embed
injectively into new colors F_(n+1) by e_n; thus the required color
embeddings impose their usual cardinality restriction. There is no extra
bound, rate, or regularity hypothesis on the field sizes.

At stage n the ambient group is G_n, with

    G_0=G, G_(n+1)=G_n x F_(n+1)^2.

Extend the old color family B_n by empty colors outside e_n(F_n), then
apply the existing affine-line recoloring with parameters tau_n and
alpha_n != 0. An old point a in color u contributes, for every row x,

    (a, (x, e_n(u)*x+tau_n*e_n(u)^2))

in new color v=e_n(u)+alpha_n*x. Every one of these inherited points must
be retained. Arbitrarily many further points may be added colorwise.
No disjointness or upper-cap hypothesis is needed for the peak propagation.

## 2. Two independent peak lower bounds

ChangingFieldLineStepExplore adapts the old mixed-count domination to the
injective color extension. Any old mixed count survives in every prescribed
pair of new colors. Counts between distinct old labels contribute twice
to a new self-count. Consequently, from any nonempty starting color at
stage N, stage N+2k has an inherited same-color peak at least 2^k.
The two fields at successive steps need not be equal.

There is also a field-size peak. A single retained old point contains an
entire affine line of q=|F_(n+1)| points in the new uncolored union. The
pairs at rows x and -x all have target

    (a+a, (0, 2*tau_n*e_n(u)^2)).

Their first endpoints are distinct, so the actual ordered self-count at
that target is at least q. This does not require alpha_n != 0, odd
characteristic, disjoint colors, or absence of added points.

## 3. Why choosing huge fields cannot outrun doubling

Put T_n=log|G_n|. Then

    T_(n+1)=T_n+2 log q_n.

If an eventual global cap K+C T_n existed, the field-size peak would give

    q_n <= K+C T_(n+1).

After replacing K,C with harmless nonnegative larger constants, set
Z_n=K+C T_n. The scalar argument proves, uniformly for every q_n>0,

    Z_(n+1)+A <= (5/4)(Z_n+A),
    A=16C log(16(C+1))+1 > 0.

It follows from log(q/d)<=q/d-1 with d=16(C+1), not from an unproved
assumption about the growth rate of q_n. Thus Z_n+A grows at most as
(5/4)^n. At even stages this cannot dominate 2^k, because

    ((5/4)^2/2)^k=(25/32)^k -> 0.

The argument can start after any finite number of discarded stages.

## 4. Checked endpoint

Erdos66ChangingFieldLogCap.no_eventual_log_cap rules out every eventual
cap K+C log|G_n| on the actual self-count of the uncolored union.

Erdos66ChangingFieldLogCap.arbitrarily_late_log_cap_violation states that
for every N, some n>=N and some actual target violate that cap.
For changing fields this is an arbitrarily-late-violation theorem, not an
assertion that every sufficiently large stage violates the cap.

## Scope

This closes the growing-field escape for the specified FULL affine-line
iteration with injective color changes. It does not cover clipping or
removing inherited points, changing the old-coordinate copies as a
function of the row, noninjective color changes, or completely unrelated
new operators. It also does not extend the older arbitrary-graph routing
obstruction to changing fields: the field-size peak here uses line geometry.

These are finite product-group counts. No transport of the peaks through
ordinary integer carries is asserted. In particular this is not a
universal statement about subsets of the natural numbers, and it is not
a disproof of Erdős 66.

## Infinite-construction review in this continuation

The newly checked universal Bernstein operator still takes its integer
coarse profile as input and preserves prefixes only for a fixed operator.
It did not supply the quantifiers in
Erdos66Compactness.conjecture_iff_finite_prefixes: a single nonzero
coefficient and the entire threshold function must precede the final cutoff.

Prefix patching at much larger scales leaves an intermediate window that
is not controlled by the available patch estimate. The existing conditional
first-window theorem still requires predictive mixed means and a sufficient
concentration budget; neither follows from past self-count accuracy.
No stronger prefix-extension assertion was proved in this review.

There is still no compatible changing-palette construction, uniform
sublogarithmic quadratic Boolean rounding, sharp repair construction
meeting the completion criterion, or universal contradiction.

## Subsequent non-Cartesian quadratic-lift check

QuadraticFieldLiftProgress.md records a checked 22-declaration investigation
of a genuine quadratic-field parabola lift. Its individual joint cap stays
two and its old slice is exact, so it is not the full affine-line model.
But all old scalars become squares in the quadratic extension; unchanged
old label unions have exact off-slice holes and a double nominal count at
an old target. This does not exclude fresh-label or density-changing
constructions and does not settle Spec.lean.
