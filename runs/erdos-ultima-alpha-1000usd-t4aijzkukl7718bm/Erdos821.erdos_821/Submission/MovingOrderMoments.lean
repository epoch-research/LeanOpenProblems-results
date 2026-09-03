import Submission.FiniteOrderMixtures

/-!
# Why choosing the moment order after the scale is insufficient

For a fixed scale, the factorial-normalized requested lower bound tends to
zero as the order tends to infinity. The single prime 2 therefore already
satisfies a scale-first version of the moment hypothesis. This is an
unconditional quantifier check, not the fixed-order input needed for Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 2000000

lemma shiftedPrimeMoment_ge_one (k X : ℕ) (hX : 2 ≤ X) :
    1 ≤ shiftedPrimeMoment k X := by
  have h2 : 2 ∈ (X+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
  have h := Finset.single_le_sum (s := (X+1).primesBelow)
    (f := fun p : ℕ => (tau k (p-1) : ℝ)) (fun p _ => Nat.cast_nonneg _) h2
  have hτ : tau k 1=1 := (tau_multiplicative k).map_one
  simpa only [show 2-1=1 by omega, hτ, Nat.cast_one, shiftedPrimeMoment] using h

/-- At every fixed scale the proposed factorial-normalized target vanishes
as the order grows, regardless of the value of theta. -/
lemma tendsto_fixed_scale_moment_target (θ : ℝ) (X : ℕ) (hX : 2 ≤ X) :
    Tendsto (fun k : ℕ =>
      θ^k*(X : ℝ)*(Real.log X)^(k-2)/(k.factorial : ℝ)) atTop (𝓝 0) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have ht := (FloorSemiring.tendsto_pow_div_factorial_atTop (θ*Real.log X)).const_mul
    ((X : ℝ)/(Real.log X)^2)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hp : (Real.log (X : ℝ))^k = (Real.log X)^(k-2)*(Real.log X)^2 := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [mul_pow, hp]
  field_simp

/-- The prime 2 alone meets the target at every fixed scale once the order
is chosen sufficiently large. -/
theorem eventually_order_target_le_one (θ : ℝ) (X : ℕ) (hX : 2 ≤ X) :
    ∀ᶠ k : ℕ in atTop,
      θ^k*(X : ℝ)*(Real.log X)^(k-2)/(k.factorial : ℝ) ≤ 1 := by
  filter_upwards [(tendsto_fixed_scale_moment_target θ X hX).eventually_lt_const
    (by norm_num : (0 : ℝ) < 1)] with k hk
  exact hk.le

/-- This is unconditional, but its quantifier order is NOT the cofinal
fixed-order moment hypothesis. -/
theorem every_scale_has_arbitrarily_large_successful_orders (θ : ℝ) (X : ℕ)
    (hX : 2 ≤ X) (B : ℕ) :
    ∃ k : ℕ, B ≤ k ∧ 2 ≤ k ∧
      θ^k*(X : ℝ)*(Real.log X)^(k-2)/(k.factorial : ℝ) ≤ shiftedPrimeMoment k X := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_order_target_le_one θ X hX)
  let k := max (max B 2) K
  have hkK : K ≤ k := le_max_right _ _
  refine ⟨k, (le_max_left B 2).trans (le_max_left _ _),
    (le_max_right B 2).trans (le_max_left _ _), ?_⟩
  exact (hK k hkK).trans (shiftedPrimeMoment_ge_one k X hX)

/-- On the exact dyadic scales of the sufficient criterion, allowing the
order to depend on the scale is already trivially satisfied. -/
theorem moving_order_dyadic_lower (θ : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (B M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ k : ℕ, B ≤ k ∧ 2 ≤ k ∧
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L) := by
  let L := max M 1
  have hL : 1 ≤ L := le_max_right _ _
  have hX : 2 ≤ momentScaleX t L := by
    unfold momentScaleX
    have he : 1 ≤ 128*t*L := Nat.mul_pos (Nat.mul_pos (by decide) ht) hL
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) he
  exact ⟨L, le_max_left _ _, every_scale_has_arbitrarily_large_successful_orders θ _ hX B⟩

end Erdos821.HigherDivisors
