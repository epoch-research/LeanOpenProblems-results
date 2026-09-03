import Submission.MovingOrderMoments

/-! Exact-type and axiom checks for the order-mixture and quantifier results. -/

#print axioms Erdos821.HigherDivisors.exists_component_le_of_weighted_sum_le
#print axioms Erdos821.HigherDivisors.cofinal_geometric_moments_of_finite_mixture
#print axioms Erdos821.HigherDivisors.finite_mixture_of_cofinal_geometric_moments
#print axioms Erdos821.HigherDivisors.finite_mixture_iff_cofinal_geometric
#print axioms Erdos821.HigherDivisors.erdos_821_of_finite_order_mixtures
#print axioms Erdos821.HigherDivisors.exists_cutoff_all_finite_mixtures_small
#print axioms Erdos821.HigherDivisors.shiftedPrimeMoment_ge_one
#print axioms Erdos821.HigherDivisors.tendsto_fixed_scale_moment_target
#print axioms Erdos821.HigherDivisors.eventually_order_target_le_one
#print axioms Erdos821.HigherDivisors.every_scale_has_arbitrarily_large_successful_orders
#print axioms Erdos821.HigherDivisors.moving_order_dyadic_lower

open Erdos821.HigherDivisors in
example : FiniteMixtureMomentLower ↔ CofinalGeometricMomentLower :=
  finite_mixture_iff_cofinal_geometric

open Erdos821.HigherDivisors in
example (θ : ℝ) (t : ℕ) (ht : 1 ≤ t) (B M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ k : ℕ, B ≤ k ∧ 2 ≤ k ∧
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L) :=
  moving_order_dyadic_lower θ t ht B M
