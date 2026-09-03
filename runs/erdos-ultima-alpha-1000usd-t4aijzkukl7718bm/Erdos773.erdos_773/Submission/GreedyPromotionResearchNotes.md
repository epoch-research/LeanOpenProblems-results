# Nonlinear promotion defects: three-to-two tail now verified

This is NOT a settlement of Erdős 773. Spec.lean remains unchanged with its
sole admission for 0<epsilon<=1/3. The strongest actual lower bound remains
N^(2/3)/1200. The new estimates are stopped-process error estimates, not a
new running-time or Sidon extraction theorem.

## New clean modules and verification

- GreedyTripleWitnessTails.lean: 6 printed audits.
- GreedyPromotionWitnesses.lean: 9 printed audits.
- GreedyPromotionTails.lean: 2 printed audits.
- GreedyPromotionScales.lean: 6 printed audits.

All four modules compile without errors, warnings, or admissions. All 23
printed audits use only propext, Classical.choice, and Quot.sound. They do
not import Spec.lean, and their .olean files are built.

Logs:

    /tmp/greedy-triple-witness.log
    /tmp/greedy-promotion-witnesses.log
    /tmp/greedy-promotion-tails.log
    /tmp/greedy-promotion-scales.log
    /tmp/greedy-promotion-final-audit.log

## 1. Two-stage packing for three-vertex witnesses

For arbitrary indexed supports C(i) of cardinality three, i in T, suppose
that every distinct pair of vertices belongs to at most P indexed supports.
Single-vertex incidences may be large; repeated supports retain multiplicity.

For stopped selection ratio p=t/L, with L>0 and t<=L, the proved bound is

    Pr(selected support count > 6 P l k)
      <= V * (3 |T| p^2/(l+1))^(l+1)
           + (3 |T| p^3/(k+1))^(k+1).

Here V is the ambient vertex count. This is a finite expectation bound on
an event indicator; no independence of witness-inclusion events is assumed.

Proof structure:

1. At a designated vertex a, delete a from every incident witness. These
   two-vertex link supports have single-vertex incidence at most P.
2. The existing packing theorem bounds their selected count above 2Pl.
3. If all selected incidences are <=2Pl but there are >6Plk selected
   three-vertex witnesses, packing the SELECTED family gives a disjoint
   selected (k+1)-subfamily.
4. Apply the stopped-process inclusion bound to its union, and union-bound
   over link failures and disjoint families.

`selected_packing` is deliberately stated with a bound on selected, not
original, incidences. `packed_event_tail` does not need an incidence bound.
These are reusable interfaces for future nonlinear witness estimates.

## 2. Arithmetic-free promotion witnesses

The original hypergraph H is four-uniform, distinct edges intersect in at
most two vertices, degree(u)<=D, and pair codegrees are at most K.

For fixed u, a pattern is (e,a,f) with

    e,f in H, e != f, u in e,
    |e intersect f|>=2,
    a in e\f, a != u.

Its selected witness is

    {a} union (f\e).

The intersection hypothesis makes the witness cardinality exactly three.
All edge indices and the marked vertex are retained. The checked bounds are

    number of patterns <= 12DK,
    pair incidence of witnesses <= 24K^2.

The pair-incidence proof separates the possibilities:

* One specified vertex is the marked vertex: at most 6K^2 patterns per role.
* Both specified vertices are in f\e: at most 12K^2 patterns, by reversing
  the edge roles, choosing f through that pair, then an overlapping e and
  one of at most two marks in e\f.

No unproved arithmetic fact about square collisions is used here.

## 3. Exact connection to the state-dependent promotion defect

If an active residual three-edge e fails to promote after choosing w, the
previously proved blocked-overlap lemma gives a different f sharing w and
another residual vertex x, with f\e selected. Since e has one selected
vertex and its intersection with f is exactly {w,x}, that selected vertex
lies in e\f. It is not the available tracked vertex u. This supplies the
new three-vertex witness.

Let cost_u(I) be the number of selected patterns. It is monotone in I.
The actual state-dependent failure count obeys

    promotionDefect H I 2 u <= 2 cost_u(I).

The factor two is the number of possible co-residual choices in an active
three-edge through u. This theorem keeps failed promotions due to the death
of u; it does not count only safe choices and silently discard those errors.

## 4. All-prefix tail

`GreedyPromotionTails.prefix_promotion_tail` proves, with p=t/L,

    Pr(exists J subset I: promotionDefect H J 2 u > 288 K^2 l k)
      <= V*(36DK p^2/(l+1))^(l+1)
           + (36DK p^3/(k+1))^(k+1).

Every selected subset is covered, hence every prefix of any path realizing
I. The promotion defect itself need not be monotone; the proof uses its
monotone witness-count upper bound instead.

`prefix_promotion_tail_of_le` permits any larger error threshold.

## 5. Explicit polynomial-scale regime

For m>=36 assume

    D <= m^300, K <= m^3, p <= 1/m^97.

Take

    l=m^112, k=m^15.

The two exponential bases are at most 36/m^3 <= 1/m^2. The deficit threshold
is at most 288m^133. Thus at a designated u,

    Pr(exists J subset I: promotionDefect H J 2 u > 288m^133)
      <= (V+1)*(1/m^2)^(m^15+1).

Summing over all V vertices gives

    V(V+1)*(1/m^2)^(m^15+1).

If additionally V<=m^A and A<=m, the last expression is <=2/m^2. This is
proved by `all_vertex_polynomial_tail`, not merely an asymptotic heuristic.
It still does NOT establish that the stopped process reaches t vertices.

## Remaining immediate nonlinear work

1. Failed promotions from residual size FOUR to THREE are not controlled
   yet. Their basic overlap witness has only two selected vertices. The
   three-witness theorem above does not apply to that term.
2. Generalize higher local-degree drift and variance estimates, retaining
   both the new promotion errors and previously proved duplicate errors.
3. Establish nonlinear trajectory tracking and eliminate early stopping.
4. The unit N^(2/3) endpoint also needs sharp average-degree and horizon
   constants. Removing linearity alone does not remove the old trimming
   or conservative time-budget losses.
5. Even the endpoint would leave every 0<epsilon<1/3 of the main problem.

## Concrete next approach for the two-vertex witnesses (not proved yet)

For four-to-three failures, index overlapping pairs (e,f) with u in e and
use f\e as witness. Expected finite bounds are |T|<=6DK, support size two,
and pair incidence <=6K^2. The witness counting and its connection to the
actual defect still need formalization.

A direct use of the two-stage packing bound is too wasteful in the useful
power regime: high-degree stars can dominate. One possible finite proof is
to split the two-witness multigraph into heavy and light original vertices.
For a general family with E indexed edges and multiplicity cap P:

* Let heavy vertices have original degree >h; there are at most 2E/h.
* Bound selected link counts globally by P*l0, and at light vertices by P*l1,
  using one-vertex link witnesses and the existing packing theorem.
* Bound the number of selected heavy vertices by s using inclusion tails.
* Heavy selected edges contribute at most s*P*l0.
* Pack remaining selected light edges, obtaining a tail above 2P*l1*k.

Proposed resulting error bound for count >s*P*l0+2P*l1*k is the sum of:

    V*(3E p/(l0+1))^(l0+1),
    V*(3h p/(l1+1))^(l1+1),
    (3|heavy| p/(s+1))^(s+1),
    (3E p^2/(k+1))^(k+1).

This is only a plan; none of these combined two-witness estimates has been
proved in this continuation. At E~D, p~D^-1/3, h~D^1/2, choices just above
l0~D^2/3, l1~D^1/6, s~D^1/6, k~D^1/3 suggest an error scale about D^5/6,
which is smaller than the D-scale four-edge promotion term. All margins,
codegree factors, probability sums, and prefix arguments must still be checked.
