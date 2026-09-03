# Four-to-three promotion tails and nonlinear higher drift

This is NOT a settlement of Erdős 773. Spec.lean is unchanged, with its sole
admission for 0<epsilon<=1/3. No new actual Sidon lower bound or endpoint has
been proved; the strongest actual bound remains N^(2/3)/1200.

## New clean modules

All seven modules compile without errors, warnings, or admissions, and their
33 printed audits use only propext, Classical.choice, and Quot.sound. None
imports Spec.lean. Their .olean files are built.

- GreedyTwoWitnessPacking.lean: 5 printed audits.
- GreedyTwoWitnessTails.lean: 5 printed audits.
- GreedyHigherPromotionWitnesses.lean: 5 printed audits.
- GreedyHigherPromotionTails.lean: 2 printed audits.
- GreedyHigherPromotionScales.lean: 6 printed audits.
- GreedyNonlinearGuards.lean: 3 printed audits.
- GreedyCodegreeHigherDrift.lean: 7 printed audits.

Logs:

    /tmp/greedy-two-packing.log
    /tmp/greedy-two-tails.log
    /tmp/greedy-higher-promotion-witnesses.log
    /tmp/greedy-higher-promotion-tails.log
    /tmp/greedy-higher-promotion-scales.log
    /tmp/greedy-nonlinear-guards.log
    /tmp/greedy-codegree-higher-drift.log
    /tmp/greedy-higher-promotion-final-audit.log

## 1. Heavy/light packing is now proved

For an indexed family T of two-vertex witnesses C(i), keep all multiplicities
and assume pair incidence at most P. Let E>=|T|, p=t/L, L>0, t<=L. Define
heavy vertices to have original incidence >h, where h>0. The verified
incidence identity gives

    h*|heavy| <= 2|T|.

`packing_of_split` first proves a deterministic statement for an arbitrary
heavy set A. If all selected links have size at most M0, links at vertices
outside A have size at most M1, and at most s vertices of A are selected,
then more than s*M0+2*M1*k selected witnesses imply a disjoint selected
(k+1)-subfamily. The proof covers heavy selected witnesses by the selected
heavy vertices and packs only the remaining light witnesses.

`GreedyTwoWitnessTails.two_tail` then proves

    Pr(selected witness count > s*(P*l0)+2*(P*l1)*k)
      <= V*(3E p/(l0+1))^(l0+1)
       + V*(3h p/(l1+1))^(l1+1)
       + (6E p/(h*(s+1)))^(s+1)
       + (3E p^2/(k+1))^(k+1).

The four terms respectively control global selected links, light selected
links, the number of selected heavy vertices, and disjoint selected witnesses.
These are finite stopped-process expectation bounds, not independence
assumptions. The previously proposed heavy/light estimate is now checked.

## 2. Actual promotion witnesses

For fixed tracked u, index overlapping original pairs (e,f), with u in e,
e!=f, and |e intersect f|>=2. The witness is f\e. With four-uniformity,
intersection at most two, degree(u)<=D, and pair codegrees at most K:

    number of patterns <=6DK,
    witness cardinality =2,
    witness pair incidence <=6K^2.

The pair-incidence estimate reverses e and f: a specified pair in f\e
constrains f to at most K original edges, each with at most 6K overlaps.
All original edge indices are retained.

`promotionDefect_bound` is slightly more general: for ANY target size j>=2,

    promotionDefect H I j u <= j*cost_u(I),

where cost_u is this monotone two-witness count. No four-uniformity or
intersection hypothesis is needed for this domination itself. Those
hypotheses are used to bound witness cardinality and pattern counts.

## 3. Four-to-three all-prefix tail

The new prefix event is

    exists J subset I, threshold < promotionDefect H J 3 u.

`GreedyHigherPromotionTails.prefix_promotion_tail` controls it at threshold

    18K^2*l0*s + 36K^2*l1*k

by

    V*(18DK p/(l0+1))^(l0+1)
    + V*(3h p/(l1+1))^(l1+1)
    + (36DK p/(h*(s+1)))^(s+1)
    + (18DK p^2/(k+1))^(k+1).

The promotion deficit need not be monotone. Its monotone witness upper
bound controls all selected subsets, hence all path prefixes. There is also
`prefix_promotion_tail_of_le` for a larger error threshold.

## 4. Explicit scales, compatible with the previous promotion bound

Assume m>=36,

    D<=m^300, K<=m^3, p<=m^-97.

Choose

    h=m^150,
    l0=m^209,
    l1=m^56,
    s=m^59,
    k=m^112.

All four exponential bases are <=1/m^2. The error threshold is at most
54m^274. Thus the designated-vertex prefix probability is at most

    2(V+1)*(1/m^2)^(m^15+1).

The exponent has been weakened to m^15+1 to reuse the already verified
volume estimate. If V<=m^A and A<=m, the sum of all designated-vertex error
probabilities is <=4/m^2. This is `all_vertex_polynomial_tail`.

## 5. All nonlinear error guards combined

`GreedyNonlinearGuards.expectation_badCost` proves total cost <=8/m^2:

    local duplicates and common neighbors: <=2/m^2,
    three-to-two failed promotions:        <=2/m^2,
    four-to-three failed promotions:       <=4/m^2.

The combined `controlled_run` obtains an ACTUAL reachable independent state
I for the stopped process. It explicitly retains

    |I|=t OR |available(I)|<L.

For every J subset I it gives

* duplicateExcess_J(u)<=16m^21 for every u;
* commonDegree_J(u,v)<=16m^21 for distinct available u,v;
* promotionDefect_J(2,u)<=288m^133 for every u;
* promotionDefect_J(3,u)<=54m^274 for every u.

This certificate does NOT exclude early stopping and does NOT prove the
local degrees follow their trajectories. The expectation estimate, not just
the existence statement, is available for combining with later martingale
failure bounds.

## 6. Higher local-degree drift now does not require linearity

Write d_j(u) for original-edge incident counts, P_j(u) for promotionDefect,
c(u,v) for common closure neighbors, and

    W_j(u)=sum_{e incident_j(u)} sum_{x in residual(e)\{u}} |closes(x)|.

For every j>=3, with common-neighbor bound C, the new module proves

    sum_safe localLost_j(u,w) <= (j-1)d_j(u)+W_j(u),

    W_j(u) <= sum_safe localLost_j(u,w)
              +(choose(j,2)C+j-1)d_j(u).

No linearity assumption or uncounted internal-closure term is present.
The per-edge error j-1 is sufficient to absorb the extra unsafe endpoint
and omission of the direct residual-choice contribution in the lower bound.
The proof uses two set inclusions and a Bonferroni union estimate, rather
than claiming the linear disjoint-union identity still holds.

Combining with exact promotion balance gives

    j*d_(j+1)(u)-P_j(u)-(j-1)d_j(u)-W_j(u)
      <= survivalDrift_j(u)
      <= j*d_(j+1)(u)-P_j(u)-W_j(u)
         +(choose(j,2)C+j-1)d_j(u).

If l<=d_2(x)<=h and duplicateExcess(x)<=E at available x, then

    (l-E)(j-1)d_j(u)<=W_j(u)<=h(j-1)d_j(u).

`survival_drift_profile_bounds` packages the resulting conditional interval.
These are finite drift bounds; they do not assert the profile hypotheses
hold along a long trajectory.

## Next concrete work

1. Complete an efficient nonlinear TWO-degree drift interval. The exact
   identity already exists in GreedyCodegreeDrift, but the term

       sum_{w safe} lostDuplicate(u,w)

   should not be bounded by E*|available|: that loses too much. By swapping
   the common-neighbor sum it should equal

       sum_{x in closes(u)} (pairReps(u,x).card-1)
                            * |closes(x) intersect safeChoices(u)|,

   and hence be at most h*duplicateExcess(u) when closure degrees <=h.
   This weighted identity and bound are NOT proved yet.
2. Update the tracked-state one-step variance bounds using the new
   bounded-codegree increment estimates. The tracked-state and freezing
   interfaces are generic; the old linear drift/variance instantiations
   must not be applied unchanged.
3. Check numerical profile conditions under the four nonlinear guards,
   lift the error-tail costs to the tracked process, prove long-time
   tracking, and eliminate early stopping.
4. The endpoint still requires sharp average-degree and horizon constants,
   not merely the removal of linearization. All smaller epsilon require
   a new exponent argument beyond a generic N^(2/3) lower bound.

Technical note: in one natural-valued sum, rewriting nsmul_eq_mul introduced
a redundant Nat-to-Nat cast. `norm_cast at hs'` was needed before omega.
No debugging trace remains in the final modules.
