import Submission.GaussianDirectionWeights
import Submission.GaussianRadialBins

/-! Weighted reciprocal sums for the primitive Gaussian-direction count. -/
namespace Erdos773.GaussianRadialCounting
open Finset GaussianDirectionWeights GaussianRadialBins
set_option maxHeartbeats 2000000
noncomputable section

lemma bin_index {u v : ℕ} (hu : 0 < u) (hv : v < u) :
    40*v/u < 40 ∧ u*(40*v/u)  ≤  40*v ∧ 40*v < u*(40*v/u+1) := by
  exact ⟨(Nat.div_lt_iff_lt_mul hu).mpr (by omega),Nat.mul_div_le _ _,
    Nat.lt_mul_div_succ _ hu⟩

lemma weighted_height_sum (u : ℕ) (hu : 0 < u) :
    (∑ v ∈ Icc 1 (u-1), (weight u v : ℝ)*(height (40*v/u) : ℝ))  ≤ 
      (row u : ℝ)*((u:ℝ)/8400+1)*(793/25) := by
  have hb (v : ℕ) (hv : v ∈ Icc 1 (u-1)) := bin_index hu (show v<u by
    have hh := (mem_Icc.mp hv).2
    omega)
  have hf := sum_fiberwise_of_maps_to
    (fun v hv => mem_range.mpr (hb v hv).1)
    (fun v => (weight u v : ℝ)*(height (40*v/u) : ℝ))
  rw [← hf]
  calc
    _ = ∑ i ∈ range 40, (height i : ℝ)*
        (∑ v ∈ (Icc 1 (u-1)).filter (fun v => 40*v/u=i), (weight u v : ℝ)) := by
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]
      ring
    _  ≤  ∑ i ∈ range 40, (height i : ℝ)*((row u : ℝ)*((u:ℝ)/8400+1)) := by
      apply sum_le_sum
      intro i hi
      have hi40 := mem_range.mp hi
      have hpos : (0:ℝ)  ≤  height i := (Rat.cast_nonneg (K:=ℝ)).mpr (height_nonneg i)
      apply mul_le_mul_of_nonneg_left _ hpos
      apply weighted_bin
      intro v hv
      obtain ⟨hv,hvi⟩ := mem_filter.mp hv
      have ht := hb v hv
      rw [hvi] at ht
      exact ⟨ht.2.1,ht.2.2.le⟩
    _ = (row u : ℝ)*((u:ℝ)/8400+1)*(∑ i ∈ range 40, (height i : ℝ)) := by
      rw [← sum_mul]
      ring
    _  ≤  _ := mul_le_mul_of_nonneg_left height_sum_real
      (mul_nonneg (Nat.cast_nonneg _) (by positivity))

lemma row_reciprocal_bound (u : ℕ) (hu : 0<u) :
    (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2))  ≤ 
      (793/210000:ℝ)*(row u:ℝ)/u+(33306/5:ℝ)/(u:ℝ)^2 := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hb : (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2))  ≤ 
      (∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)*(height (40*v/u):ℝ))/(u:ℝ)^2 := by
    rw [sum_div]
    apply sum_le_sum
    intro v hv
    have hh := mul_le_mul_of_nonneg_left
      (reciprocal_bound hu (Nat.mul_div_le (40*v) u)) (Nat.cast_nonneg (weight u v): (0:ℝ) ≤ weight u v)
    simpa only [mul_one_div,mul_div_assoc] using hh
  have hs := div_le_div_of_nonneg_right (weighted_height_sum u hu) (sq_nonneg (u:ℝ))
  have hr : (row u:ℝ) ≤ 210 := by exact_mod_cast row_le u
  have heq : ((row u:ℝ)*((u:ℝ)/8400+1)*(793/25))/(u:ℝ)^2 =
      (793/210000:ℝ)*(row u:ℝ)/u+(793/25:ℝ)*(row u:ℝ)/(u:ℝ)^2 := by
    generalize (row u : ℝ) = R
    field_simp
    ring
  rw [heq] at hs
  have herr : (793/25:ℝ)*(row u:ℝ)/(u:ℝ)^2  ≤  (33306/5:ℝ)/(u:ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith only [hr]
  exact (hb.trans hs).trans (add_le_add le_rfl herr)

def triangleSum (M : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 M, ∑ v ∈ Icc 1 (u-1), (weight u v:ℝ)/((u:ℝ)^2+(v:ℝ)^2)

/-- A rational leading coefficient strictly below one third. -/
theorem triangle_sum_bound {M : ℕ} (hM : 1 ≤ M) :
    triangleSum M  ≤  (83/250:ℝ)*(1+Real.log M)+14000 := by
  have hs := sum_le_sum (s := Icc 1 M) (fun u hu => row_reciprocal_bound u (by have := mem_Icc.mp hu; omega))
  change triangleSum M  ≤  _ at hs
  have he : (∑ u ∈ Icc 1 M, ((793/210000:ℝ)*(row u:ℝ)/u+(33306/5:ℝ)/(u:ℝ)^2)) =
      (793/210000:ℝ)*(∑ u ∈ Icc 1 M, (row u:ℝ)/u)+
      (33306/5:ℝ)*(∑ u ∈ Icc 1 M, 1/(u:ℝ)^2) := by
    rw [sum_add_distrib,mul_sum,mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intros <;> ring
  rw [he] at hs
  have hr := row_log M
  have hi := PeriodicCollisionWeights.inverse_square_sum M
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  nlinarith only [hs,hr,hi,hlog]

#print axioms weighted_height_sum
#print axioms row_reciprocal_bound
#print axioms triangle_sum_bound
end
end Erdos773.GaussianRadialCounting
