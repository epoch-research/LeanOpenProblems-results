import Submission.SubsetProductMass

/-!
# Limits of fixed-order elementary symmetric masses

A vanishing bound for individual nonnegative weights removes repeated-index
collisions. The order is fixed before the limit is taken.
-/
open Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
set_option maxHeartbeats 3000000

lemma elementaryMass_succ_upper (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (r : ℕ) :
    ((r+1 : ℕ) : ℝ)*elementaryMass P w (r+1) ≤
      elementaryMass P w r*(∑ p ∈ P, w p) := by
  rw [elementaryMass_succ_identity, elementaryMass, sum_mul]
  apply sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ => hw p hp))
    (prod_nonneg (fun p hp => hw p ((mem_powersetCard.mp hS).1 hp)))

lemma elementaryMass_factorial_upper (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (r : ℕ) :
    elementaryMass P w r ≤ (∑ p ∈ P, w p)^r/(r.factorial : ℝ) := by
  induction r with
  | zero => simp [elementaryMass_zero]
  | succ r ih =>
    have hh := (elementaryMass_succ_upper P w hw r).trans
      (mul_le_mul_of_nonneg_right ih (sum_nonneg hw))
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < r+1)).mp
    convert hh using 1
    · push_cast; ring
    · rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp

/-- The hypotheses control every weight, not just an average weight. -/
theorem tendsto_elementaryMass_of_small_weights (P : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (β : ℕ → ℝ) (μ : ℝ)
    (hw : ∀ m p, p ∈ P m → 0 ≤ w m p)
    (hβ : ∀ m p, p ∈ P m → w m p ≤ β m)
    (hS : Tendsto (fun m => ∑ p ∈ P m, w m p) atTop (𝓝 μ))
    (hβlim : Tendsto β atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun m => elementaryMass (P m) (w m) r) atTop (𝓝 (μ^r/(r.factorial : ℝ))) := by
  induction r with
  | zero => simpa only [elementaryMass_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ r ih =>
    have hr : (0 : ℝ) < r+1 := by positivity
    have hlow := (ih.mul (hS.sub (hβlim.const_mul (r : ℝ)))).div_const ((r : ℝ)+1)
    have hupp := (ih.mul hS).div_const ((r : ℝ)+1)
    have he : (μ^r/(r.factorial : ℝ)*μ)/((r : ℝ)+1) = μ^(r+1)/((r+1).factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    simp only [mul_zero, sub_zero, he] at hlow hupp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
    · intro m
      apply (div_le_iff₀ hr).mpr
      have hh := elementaryMass_succ_lower (P m) (w m) (hw m) (β m) (hβ m) r
      convert hh using 1
      push_cast
      ring
    · intro m
      apply (le_div_iff₀ hr).mpr
      have hh := elementaryMass_succ_upper (P m) (w m) (hw m) r
      convert hh using 1
      push_cast
      ring

end Erdos821
