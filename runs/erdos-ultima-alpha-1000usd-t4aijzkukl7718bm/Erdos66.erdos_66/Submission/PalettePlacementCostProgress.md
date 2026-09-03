# Integer placement cost of a dense palette member

The conjecture in `Spec.lean` remains unproved and undisproved. Its statement
and original `sorry` have not been changed.

## Checked results

`PalettePlacementCostExplore.lean`, namespace `Erdos66PalettePlacementCost`:

* `window_pair_mass`: for a finite integer set F in [a,a+M),

      |F|^2 = sum_{2a <= n < 2a+2M} r_F(n).

* `finite_window_cost`: if F is contained in A and

      r_A(n) <= K+C log(n+2),   C>=0,

  then

      |F|^2 <= 2M [K+C log(2a+2M+2)].

* `placed` maps a cyclic member B modulo M to {a+b.val : b in B}.
  For M>0, this preserves cardinality and lies in [a,a+M).
  `palette_member_cost` applies the preceding bound to this actual integer
  realization, without requiring cyclic flatness.

* `positive_density_cost`: if |B| >= rho M, rho>=0, then

      rho^2 M <= 2K+2C log(2a+2M+2).

* `positive_density_exponential_cost`: for C>0 this implies

      exp((rho^2 M-2K)/(2C)) <= 2a+2M+2.

* `eventually_no_polynomial_dense_window`: for fixed K,C,rho,d with
  C>=0, rho>0, and positive natural d, all sufficiently large M admit NO
  such window with a<=M^d and |F|>=rho M. The threshold is uniform in A,F,a.
  This is stated for arbitrary finite windows, not just cyclic palettes.

The file compiles and has a built olean. `PalettePlacementCostAxiomCheck.lean`
audits the main statements; only propext, Classical.choice, and Quot.sound
occur.

## Consequence and scope

A fixed positive-density member of the completed cyclic palette cannot be
placed as a full block at a fixed polynomial scale in its width under a
fixed logarithmic upper envelope. In particular, the complete palette
cannot be inserted wholesale into the existing polynomial-scale annuli.

This does not rule out palettes whose used densities tend to zero,
nonliteral realizations, or other compatible inhomogeneous constructions.
It is not a negation of the original conjecture. The missing global
scale-transition construction remains missing.

## Sharper consequence at the actual sparse starting levels

Three further results also compile and pass the axiom audit:

* `eventually_no_oversized_logarithmic_window`: if lambda > 2 C d, then
  uniformly for all sufficiently large M, no block at a<=M^d under the
  envelope can satisfy |F|^2 >= lambda M log M.

* `logarithmic_window_coefficient_le`: for a sequence of such placements
  with M tending to infinity, if |F|^2/(M log M) tends to beta, then
  beta <= 2 C d.

* `eventually_no_high_palette_level`: suppose eta<=1 and

      2 C d < (1-eta) c0 H^2.

  For all sufficiently large M, no literal placement of a cyclic member B
  at a<=M^d under the envelope can simultaneously have

      mu >= c0 log M,
      |r_cyclic(B,B;z)-mu H^2| <= eta mu H^2   for every z.

  This follows by summing the cyclic counts to obtain the actual cardinality
  lower bound, then applying the integer window bound. It does not assume
  that the cyclic carry fibers split evenly.

This tests the member C_H where the completed palette's multiplicative
coverage begins, not just its eventual positive-density members. With
mu/log M near c and outer envelope coefficient C near c, literal placement
requires approximately H^2<=2d. Thus a large starting index H cannot be
used at a fixed small polynomial exponent even though C_H remains sparse.
For the explicit completion budget with c fixed, the selected H grows as
accuracy is tightened, while a fixed polynomial placement exponent cannot
pay this cost.

This still does not exclude sparse sublevels, nonliteral realizations, or
arbitrary other infinite sets. No universal contradiction or compatible
infinite construction was obtained. A review of the existing Abel energy
and fixed-modulus necessary conditions still only yields fluctuations on
scales compatible with o(log n).
