# Near-scale prefix-independent bridges are impossible

## Original task status

The original conjecture remains unresolved. `Submission/Spec.lean` is
unchanged and contains its original `sorry`. No proof or disproof of its
existential statement has been obtained or submitted.

## New checked obstruction

For each c>0, at EVERY sufficiently large L, the following holds.
Let D be ANY set supported at or above 3L which represents every target
in [6L,8L). Then there is a finite A below 3L such that

* r_A(n)/log n <= c for EVERY natural n;
* for some 5L<=t<=6L, r_(A union D)(t)/log t > c.

D need not be finite, self-flat, or upper-bounded. The prefix A is constructed
as a Sidon set supported in (L,2L], so its self-counts are at most TWO.

Thus one cannot strengthen the row-controlled extension to a near-scale
bridge that selects D first and works for EVERY old prefix satisfying only
a global upper bound. This conclusion is not the earlier accurate-history
obstruction: the adverse prefix here DOES satisfy a global upper envelope.

## Proof

1. A basis on [6L,8L), supported above 3L, has at least sqrt(2L) points
   in [3L,5L). This follows by summing representation counts and bounding
   the total by the square of that restricted cardinality.
2. Split these points at 4L. If 2m^8<L, one half contains more than m^4
   points.
3. An arbitrary finite set with more than m^4 points has a Sidon subset F
   of cardinality m. This uses the already checked collision-avoidance
   selection theorem, with no auxiliary hit constraints.
4. Reflect F about t=5L or t=6L, depending on the half. The reflected set A
   is Sidon and lies in (L,2L]. It is disjoint from D. At t it contributes
   at least 2m mixed representations with F subset D.
5. Choose m=ceil((c+1)log L). Eventually

       2m^8<L,  2/log(2L)<=c,  c log(6L)<2m.

   The first condition follows from (log L)^8/L -> 0. The other two are
   elementary logarithmic comparisons.

## Files and main names

`NaturalSidonExtractionExplore.lean`, namespace
`Erdos66NaturalSidonExtraction`:
* `NatSidon`
* `natSidon_rep_le_two`
* `exists_natSidon_subset`
* `natReflect_sidon`
* `natReflect_mixed`

`NearScalePrefixObstructionExplore.lean`, namespace
`Erdos66NearScalePrefixObstruction`:
* `reflected_prefix_peak`
* `basis_forces_dense_half`
* `near_scale_template_not_universal`
* `eventually_obstruction_parameters`
* `eventually_no_prefix_independent_near_scale_bridge`

Both development files compile with built oleans. The principal results
are audited in `NearScalePrefixAxiomCheck.lean` using only propext,
Classical.choice, and Quot.sound.

## Limitation

The quantifier order is essential: D is fixed before the adverse A is
chosen. The theorem does NOT prohibit selecting D depending on a prescribed
A, does not prohibit a carefully compatible infinite family, and does not
prove the negation of the original conjecture. It also does not apply to
the earlier row-controlled extension, which starts far beyond the old
prefix and therefore avoids this near-scale regime.
