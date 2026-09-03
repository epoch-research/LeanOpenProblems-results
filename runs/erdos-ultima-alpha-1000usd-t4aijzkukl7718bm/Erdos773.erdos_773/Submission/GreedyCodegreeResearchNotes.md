# Nonlinear local degrees and all-prefix local duplicate tails

This is NOT a settlement of Erdős 773. Spec.lean is unchanged and still has
its sole admission for 0<epsilon<=1/3. The strongest actual lower bound is
still the previous continuation's N^(2/3)/1200. The new work below does not
yet give an actual new lower bound or the unit-coefficient endpoint.

## Motivation and endpoint scope

The current actual extraction thins to a linear hypergraph at a fixed power
of N. That loses part of the logarithm available to a sharp greedy argument.
The new work starts to remove linearity from the deterministic and finite
probability interfaces, using the existing pair-codegree bounds instead.

The proved collision coefficient C<1/12 would be sufficient for the endpoint
IF one obtained a sharp average-degree independence estimate with the
appropriate constant, without the present thinning/trimming losses. Such an
estimate is NOT proved here or assumed. Removing linearity alone would not
suffice: conservative time horizons and maximum-degree trimming also lose
constants. Even a completed endpoint would leave all 0<epsilon<1/3.

## New verified modules

All four modules compile without errors, warnings, or admissions. They do
not import Spec.lean. All 22 printed axiom audits use only propext,
Classical.choice, and Quot.sound. Their .olean files are built.

1. GreedyCodegreeLocal.lean (8 audits)
2. GreedyCodegreeDrift.lean (4 audits)
3. GreedyLocalDuplicateTails.lean (8 audits)
4. GreedyLocalErrorCertificates.lean (2 audits)

Logs:

    /tmp/greedy-codegree-local.log
    /tmp/greedy-codegree-drift.log
    /tmp/greedy-local-duplicate.log
    /tmp/greedy-local-errors.log
    /tmp/greedy-codegree-final-audit.log

## One-step estimates without linearity

Let d_j(u) retain ORIGINAL incident-edge multiplicities, c(u,w) be the
number of common neighbors in the simple residual-two closure graph, and
K bound original pair codegrees. All increment estimates below explicitly
require that u survives selection of w.

`promoted_card_le_codegree`: at most K local promotions in a step.
`lost_card_le_codegree_closes`: at most K*(|closes(w)|+1) local losses.
`incident_increment_bound`: |Delta d_j(u)| <= K*(|closes(w)|+1).

Define

    lostDuplicate(u,w)
      = sum_{x in closes(u) intersect closes(w)} (pairReps(u,x).card-1).

The exact identity is

    localLost_2(u,w) = c(u,w)+lostDuplicate(u,w).

This holds without any intersection restriction. Moreover

    lostDuplicate(u,w) <= duplicateExcess(u),
    lostDuplicate(u,w) <= (K-1)*c(u,w).

Consequently the exact one-step interval is

    -c(u,w)-lostDuplicate(u,w)
      <= Delta d_2(u)
      <= K-c(u,w)-lostDuplicate(u,w).

If c(u,w)<=C and duplicateExcess(u)<=E, then

    |Delta d_2(u)| <= K+C+E.

## Promotion defects and exact nonlinear drift

`promotionDefect H I j u` counts, for each active original (j+1)-edge
through u, the co-residual choices w != u for which the contracted residual
fails to remain entirely available. This includes choices that close u.

The checked replacement for the linear promotion identity is

    sum_{w safe for u} localPromoted_j(u,w) + promotionDefect_j(u)
      = j*d_(j+1)(u).

Thus

    survivalDrift_j(u) + sum_{w safe} localLost_j(u,w)
      + promotionDefect_j(u) = j*d_(j+1)(u).

At j=2 this gives the exact identity

    survivalDrift_2(u)
      = 2*d_3(u) - promotionDefect_2(u)
        - sum_{x in closes(u)} |closes(x)| + |closes(u)|
        + sum_{x in closes(u)} c(u,x)
        - sum_{w safe} lostDuplicate(u,w).

`blocked_overlap_witness` proves that a failed contraction of an active
residual of size at least three has a different original edge f sharing
the chosen w and another residual vertex x with e, and f\e is selected.
This is only a witness theorem so far, NOT a concentration bound for the
promotion deficit. It identifies the next missing nonlinear error term.

## Local duplicate witnesses and exponential tails

For fixed u, index a pattern by (e,v,f), with e!=f, both e and f containing
u,v, and v!=u. Its witness is the symmetric difference (e\f) union (f\e).
Unlike the earlier common-neighbor patterns, both edges contain the same
designated endpoint u. Repeated supports keep their pattern multiplicity.

Assuming four-uniformity, intersection of distinct edges at most two,
degree(u)<=D, and pair codegrees at most K, the checked bounds are:

    number of patterns <= 3DK,
    witness cardinality = 4,
    each vertex occurs in at most 4K^2 indexed witnesses.

The incidence bound splits the two roles. In the first role, choose e
through u and the witness vertex (<=K choices), v among its two other
vertices, then f through u,v (<=K choices). The second role is obtained by
swapping e and f.

`excess_bound` shows duplicateExcess(u) is at most the selected pattern count.
The pattern count is monotone in the selected set; duplicateExcess itself
need not be monotone. Therefore the existing packing theorem controls every
selected subset, including every path prefix.

For the stopped process, L>0, t<=L, and p=t/L, the new theorem gives

    E[1_{exists J subset I: duplicateExcess_J(u)>16K^2 k}]
      <= choose(3DK,k+1) p^(4(k+1))
      <= (9DK p^4/(k+1))^(k+1).

No independence of witness inclusion events is assumed.

## Actual reachable-state certificate, retaining early stopping

Combine the local duplicate tails at all V vertices with the existing
common-neighbor tails at all distinct ordered endpoint pairs. If

    V*(9DK p^4/(k+1))^(k+1)
      + V^2*(9DK p^3/(k+1))^(k+1) < 1,

there is an actual reachable independent state I such that

    |I|=t OR |available(I)|<L,

and for every J subset I:

* duplicateExcess_J(u)<=16K^2 k for every vertex u;
* c_J(u,v)<=16K^2 k for distinct available u,v.

The early-stop alternative has NOT been eliminated. This certificate is
not a running-time theorem, and does not instantiate the old linear
trajectory argument for nonlinear input.

## Other routes checked during this continuation

Norms preserve products, not sums, so a number-field norm map was not found
to transfer the formal Gaussian Sidon theorem to integers. No valid norm
construction or impossibility theorem was obtained.

The quartic length of the older explicit primitive moment example is not a
structural limitation: the already proved prime-root moment theorem gives
primitive examples at O(k^2 log^2 k). No positive construction was obtained
from that apparent gap.

## Next concrete steps

1. Bound the local promotion deficit via its selected overlap witnesses,
   including a uniform-prefix concentration estimate, not just expectation.
2. Generalize higher-local-degree drift estimates and variance budgets,
   retaining both duplicate and promotion corrections.
3. Prove actual nonlinear trajectory tracking and rule out early stopping.
4. Any endpoint claim additionally needs sharp time and average-degree
   estimates; the old thinning/trimming constants cannot be ignored.
5. The full task still needs an exponent beyond 2/3 (ultimately every
   exponent below one), or a fixed-power upper bound giving a disproof.
