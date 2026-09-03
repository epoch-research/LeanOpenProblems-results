# Integer-transfer work: status and exact limitations

`Spec.lean` is still unproved and undisproved. Its original theorem and `sorry`
remain unchanged. Nothing in these notes is a completed submission.

## Newly checked files

* `CarryExplore.lean`:
  - `sumRep_image_eq` expresses natural representation counts after an
    injective encoding as a finite pair count.
  - `integer_lift_center`: encoding `(x,y)` in `(ZMod p)^2` as
    `x.val + p*y.val` preserves the representation count at `p^2-1` exactly.
  - `integer_lift_carry_formula`: away from this central target there are two
    different low-digit carry cases, with different high-digit targets.
  - `cyclic_periodization`: for `B : Finset (ZMod p)` and `n<p`,

        r_cyclic(B,n) = r_integer(lift B,n) + r_integer(lift B,n+p).

    Flatness of the left side does not control the split on the right.

* `EmbeddingObstructionExplore.lean`:
  - Any injective map of a nonempty finite set into the reals preserving all
    its two-term additive relations forces a uniquely represented sum.
    Proof: choose a point with largest image; its double can have no other
    representation.
  - Thus the repaired finite-field flat sets, when q>=16, have no such exact
    embedding. This only rules out exact relation-preserving transfer; it
    does not rule out approximate, weighted, or multiscale constructions.

* `CumulativeExplore.lean`:
  - `cumulative_of_log_limit`: if f(n)/log(n) -> c, then
    sum_{i<n} f(i)/(n log n) -> c.
  - `cumulative_sumRep_limit` specializes this to a putative witness.
  - `normalized_count_bounds`: eventually, for any epsilon>0,

        c-epsilon <= A(n)^2/(n log n) <= 2c+epsilon,

    where A(n)=|A intersect [0,n)|. No limit for this ratio is claimed here.
  - Proof uses Stirling to bound sum log, and Mathlib's `IsLittleO.sum_range`.

* `MomentExplore.lean`:
  - For finite centered values x_a with sum x_a=0 and M points,

        2 (sum_{a,b}(x_a+x_b)^2)^2
          <= M^2 sum_{a,b}(x_a+x_b)^4.

    This is the kurtosis lower bound 2 for a sum of two independent identical
    finite distributions. The centered version for arbitrary x_a is also proved.

All listed Lean files compile. The principal results were axiom-checked and
use only `propext`, `Classical.choice`, and `Quot.sound`.

## Unformalized analytic route worth distinguishing from a solution

Classical Abelian/Tauberian reasoning should sharpen the counting-function
bounds to A(n) ~ 2*sqrt(c/pi)*sqrt(n log n). No such theorem has been formalized
here. Mathlib has Abel limits and little-o sums, but a search did not find a
Karamata Tauberian theorem.

A potential elementary obstruction to flat *cyclic prefix* models uses moments:
the uniform distribution on [0,1] has variance 1/12 and fourth central moment
1/80, violating the iid-sum inequality 2*(1/12)^2 <= 1/80. This could show that
prefix self-convolutions need a positive amount of mass above their cutoff.
The limit argument connecting this observation to prefixes has NOT been proved.
Even if proved, it would be a constraint on transfer methods, not a disproof of
the original conjecture: the expected square-root counting profile is compatible
with a nonnegligible upper tail.

No finite construction satisfying the uniform thresholds in
`CompactnessExplore.conjecture_iff_finite_prefixes` has been found.
