# Forced full-fiber overlaps and a weighted-certificate ceiling

This continuation does NOT settle Erdős 773. The original theorem in
`Spec.lean` is unchanged and still has one admission for 0<epsilon<=1/3.
No result below is an upper bound for the original maximum.

## New arithmetic construction

`FullFiberOverlap.lean`, namespace `Erdos773.FullFiberOverlap`, proves:

Let L>0, u,v in [L,2L], canonical residues r,s<q, gcd(q,v)=1, and

    r*u = s*v (mod q).

There is t in [0,q-1] with

    v*t = r (mod q),   u*t = s (mod q).

Set

    a = 3*v + floor(v*t/q) - u,
    c = 3*u + floor(u*t/q) - v.

The natural subtractions do not truncate: u<=3v and v<=3u. The four endpoint
indices a,a+2u,c,c+2v are nonnegative and at most 10L. The center identities

    q*(a+u)+r = v*(3q+t),
    q*(c+v)+s = u*(3q+t)

give the exact common square difference

    (q*(a+2u)+r)^2 - (q*a+r)^2
      = (q*(c+2v)+s)^2 - (q*c+s)^2.

`small_gap_collision` gives the endpoints bounded by 10L, without assuming
10L<=q. `small_gap_shared_difference` places them in the full index intervals
[0,q] when 10L<=q.

`gap_unique` uses the already verified Sidon property of a full unit fiber to
recover u from the difference D. This proves a genuine injection, not just
existence of a collision for each modular match.

`shortKeys q L R` counts ((r,u),(s,v)) with r<s, both labels in R, both gaps in
[L,2L], and r*u=s*v mod q. `shortKeys_embedding` embeds these into the actual
`PartialFiberSelection.crossKeys` for V_r={ (qk+r)^2 : 0<=k<=q }, preserving
both labels. Consequently both ordinary and weighted counts are bounded by
actual overlap counts (`shortKeys_card_le`, `shortKeys_weight_le`).

For prime q, 10L<=q and L>0 make every gap a unit; this is supplied by
`prime_shortKeys_weight_le`. The label-fiber unit hypotheses are retained
explicitly. No modular pair matching is needed for this injection itself.

## Weighted pigeonhole count

`FullFiberOverlapCount.lean` first proves a general finite `hash_energy` lemma.
For a finite hash h into a q-element type, with labels that distinguish every
pair of distinct colliding elements,

    (sum_a w_a)^2 <= q * (sum_a w_a^2
       + 2 sum_{label(a)<label(b), h(a)=h(b)} w_a*w_b).

This is Cauchy–Schwarz plus an exact diagonal/ordered-pair decomposition.
No sign condition on the weights is required for this identity and inequality.

Apply it to a=(r,u), h(a)=r*u mod q, w_a=p_r^2, u in [L,2L]. With K=L+1,
T=sum_r p_r^2 and U=sum_r p_r^4, the resulting theorem is

    (K*T)^2 <= q*(K*U + 2*C),

where C is the **actual** weighted full-fiber overlap cost

    C=sum_{r<s} p_r^2*p_s^2 |positiveDiffs(V_r) intersect positiveDiffs(V_s)|.

The theorem is named `full_weight_pigeonhole`. Its proof uses the short-key
injection, so it does not mistake modular aliases for actual collisions.

## Two-thirds ceiling for this expression

`FullFiberWeightedCeiling.lean` assumes:

* q is prime and q>=10;
* canonical labels r<q, with gcd(q,2r)=1;
* PairMatching q R;
* 0<=p_r<=1 for r in R;
* FULL fibers V_r of indices 0,...,q.

Set L=floor(q/10), S=sum_r p_r, and let C be the weighted cost above. The
verified estimates K>q/10, 5K<=q, U<=T<=S and |R|^2<=2q give

    S^4 <= 40*q*S + 400*C.

This is `quartic_mass_bound`. Let F=(q+1)*S-C be the nonuniform alteration
expression. If F>0, then C<=2qS and S^3<=1000q, so

    F^3 <= 8000*q^4 <= 8000*(q*(q+1))^2.

If F<=0, the same cubic bound is immediate. The resulting public theorems
include `expression_cubic_ceiling`, `expression_height_ceiling`, and
`full_expression_height_bound`. The last states, with N=q(q+1),

    sum_r p_r |V_r| - C <= 20*N^(2/3).

The cardinal |V_r|=q+1 is proved, not assumed.

## Scope — important

This bounds only the displayed independent-selection/deletion certificate on
these full fibers. It does NOT bound the actual maximum Sidon-subset size of
the union. It does NOT bound arbitrary partial-fiber constructions, and does
NOT refute the original conjecture. It concerns the common index length q;
a generalized statement for other common lengths has not been formalized.

The calculation explains why uneven full-fiber probabilities cannot improve
the exponent from 2/3. It does not justify abandoning nonuniform selection
from specially chosen partial fibers: such sets can omit the precise
endpoints supplied by `small_gap_collision`.

An initial exact-integer diagnostic counted full-fiber overlaps for prime
q=7,11,19,31,61,101. It suggested pairwise lower bounds of order q but also
large variations. No uniform pairwise asymptotic was inferred or proved.
The formal proof instead uses aggregate weighted pigeonhole counting; it
requires neither numerical conjectures nor a pairwise lower bound.

## Verification and current status

All three new files compile without warnings or admissions and have built
`.olean` files. Printed axiom audits contain only propext, Classical.choice,
and Quot.sound. They do not import the admitted Spec.lean.

Logs:

* /tmp/full-fiber-overlap.log
* /tmp/full-fiber-overlap-count.log
* /tmp/full-fiber-weighted-ceiling.log

`Spec.lean` has not changed (SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14).
No original lower exponent or fixed-power upper bound for the actual maximum
has improved, and no proof has been submitted.
