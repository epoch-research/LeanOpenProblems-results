# Exact drift and local increments for linear collision hypergraphs

This continuation does NOT settle Erdős 773. The original Spec.lean is
unchanged and still admitted for 0<epsilon<=1/3. The strongest actual lower
bound remains (5/4)N/(N log N)^(1/3), with no endpoint improvement.

## Three new clean modules

* GreedyLinearDrift.lean: 423 lines, 13 printed audits.
* GreedyLinearLocal.lean: 436 lines, 12 printed audits.
* GreedyLinearHigherDrift.lean: 266 lines, 8 printed audits.

All three compile without warnings or admissions and have built .olean
files. All 33 printed audits use only propext, Classical.choice, Quot.sound.
None imports Spec.lean. Combined log:

    /tmp/greedy-linear-drift-final-audit.log

Notation below: Q is the available cardinality, A_j the number of active
original edges with residual size j, d_j(u) the incident count at u, and
c(u,v)=|closes(u) intersect closes(v)|. H is LINEAR: distinct original edges
intersect in at most one vertex. This is stronger than the intersection-at-
most-two assumption of the previous error-tail modules. The available
controlled linearization theorem supplies such carriers but has a power
loss; linearity is not being assumed for all square collisions.

## Generic union bound with overlap correction

`union_card_lower` proves, if each pairwise intersection of distinct indexed
supports has size at most C,

    sum_i |B_i| <= |union_i B_i| + choose(number of indices,2)*C.

The induction uses the exact two-set union cardinality identity. It permits
repeated supports and does not assume independent events.

## Global drift

Linearity implies pair codegree at most one and hence

    |closes(u)| = d_2(u)                  for available u,
    duplicateExcess(u) = 0.

For j>=2, every selected vertex of an active (j+1)-edge promotes it. A
closure of another vertex of that edge would require a second original
edge sharing the same vertex pair. Thus

    sum_w |promoted_j(w)| = (j+1) A_(j+1).

The possible choices destroying an active edge e are exactly

    (e\I) union union_{u in e\I} closes(u).

For j>=3 these two parts are disjoint. For j=2 the residual pair is ALREADY
contained in the closure union, so adding a direct loss of two would be
incorrect.

Define W_j=sum_{u available} d_j(u)*d_2(u). `driftSum` is the sum over all
available choices of the change in A_j, before division by Q. If c(u,v)<=C
for distinct available u,v, then for j>=3:

    (j+1)A_(j+1)-j A_j-W_j
        <= driftSum_j
        <= (j+1)A_(j+1)-j A_j-W_j+choose(j,2) C A_j.

For j=2:

    3 A_3-W_2 <= driftSum_2 <= 3 A_3-W_2+C A_2,
    W_2 = sum_u d_2(u)^2.

The exact available-set average is Q-1-2A_2/Q when Q>0. Uniform local
degree bounds l<=d_2(u)<=h imply l*j*A_j<=W_j<=h*j*A_j. These degree bounds
are explicit hypotheses, not asserted typical behavior.

## Local updates, with the tracked vertex surviving

`incident_card_step` proves the exact balance

    d_j(u after w) + |localLost_j(u,w)|
        = d_j(u) + |localPromoted_j(u,w)|.

If w is available, u remains available after selecting w, and H is linear:

    |localPromoted_j(u,w)| <= 1,
    |localLost_j(u,w)| <= |closes(w)|+1,
    |d_j(u after w)-d_j(u)| <= |closes(w)|+1.

These are NOT asserted across the death of the tracked vertex.

At j=2 there is an exact sharper identity:

    |localLost_2(u,w)| = c(u,w),
    -c(u,w) <= d_2(u after w)-d_2(u) <= 1-c(u,w).

Hence the increment has absolute value at most C+1 when c(u,w)<=C. Original
edge indices are retained; the one-to-one correspondence with common
neighbors is proved using linearity, not assumed for nonlinear input.

## Survival drift for the local two-degree

Define safeChoices(u) as the available choices w after which u remains
available. For available u this is exactly

    available \ ({u} union closes(u)).

`survivalDrift_j(u)` sums the local increments over those choices. Equivalently
it assigns zero increment to unsafe choices. This is a definition of a
finite sum, NOT a concentration theorem or a previously constructed process
with memory. A future process freezing the last degree at vertex death must
still be constructed and analyzed explicitly.

Every incident (j+1)-edge has j safe choices promoting it, for j>=2. Therefore

    survivalDrift_j(u) + sum_{w safe} |localLost_j(u,w)| = j d_(j+1)(u).

Double-counting residual-two-graph paths gives the exact identity

    sum_{w safe} c(u,w) + d_2(u) + sum_{x in closes(u)} c(u,x)
        = sum_{x in closes(u)} d_2(x).

Consequently

    survivalDrift_2(u)
      = 2d_3(u) - sum_{x in closes(u)} d_2(x)
          + d_2(u) + sum_{x in closes(u)} c(u,x).

In particular, if neighboring degrees are between l and h and the displayed
common-neighbor counts are at most C, the drift is between

    2d_3(u) -(h-1)d_2(u),
    2d_3(u) -(l-1-C)d_2(u).

The common-neighbor correction is real and is not discarded as zero.

## Survival drift for higher local degrees

For j>=3 define

    NW_j(u) = sum_{e incident_j(u)} sum_{x in (e\I)\{u}} d_2(x).

`GreedyLinearHigherDrift` proves

    j d_(j+1)(u) -(j-1)d_j(u)-NW_j(u)
        <= survivalDrift_j(u)
        <= j d_(j+1)(u) -(j-1)d_j(u)-NW_j(u)
            +choose(j,2) C d_j(u).

To account for unsafe choices, each closure neighborhood is restricted to
safeChoices(u). Exactly c(u,x) vertices are lost from the neighborhood of
a co-residual vertex x. The remaining union-overlap correction contributes
choose(j-1,2)C per edge; adding the j-1 restrictions gives choose(j,2)C.

With uniform available two-degree bounds l<=d_2(x)<=h, the resulting drift
interval is

    j d_(j+1)(u) -(j-1)(h+1)d_j(u),
    j d_(j+1)(u) -(j-1)(l+1)d_j(u)+choose(j,2)C d_j(u).

Again, all profile bounds remain hypotheses. Dividing the finite sums by Q
would give the corresponding mean increment of the specified safe-update
rule for a uniformly chosen available vertex; it does not prove any
long-time tracking estimate.

## Remaining work and scope

The bounded-difference-multiplicity review supplied no new conversion to
Sidonness. No general rounding impossibility theorem was proved either.
In particular, selecting representations of differences independently does
not certify a common vertex subset containing all the retained pairs.

The new drift lemmas do not rule out early stopping. Missing ingredients
include a precise tracked process, a variance-sensitive martingale tail,
and differential-equation tracking with all stopping events accounted for.
Mathlib contains Azuma-Hoeffding results in Probability/Moments/SubGaussian,
but a search found no Freedman or martingale Bernstein theorem there.
A useful existing analytic input for a future finite proof is

    Real.norm_exp_sub_one_sub_id_le

in Analysis/Complex/Exponential.lean: for |x|<=1, the error in exp(x)=1+x
has absolute value at most x^2. No such concentration implementation has
been started in these modules.

Even a logarithmic-gain independence theorem would still leave the actual
near-linear exponent gap for squares. No square-specific selector or
fixed-power upper bound was found in this continuation.

Main check: /tmp/spec-linear-drift-check.log, still with the expected
admission. Spec.lean SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
No proof submission has been made.

## Subsequent concentration-tool update

A finite variance-sensitive first-crossing bound is now implemented in
FiniteFreedman, together with finite kernels, union bounds, actual path
extraction, and an exact stopped-greedy kernel/memory-lifting interface.
See FiniteFreedmanResearchNotes.md. The concrete tracked state, variance
budgets, and long-time trajectory estimates remain unproved.
