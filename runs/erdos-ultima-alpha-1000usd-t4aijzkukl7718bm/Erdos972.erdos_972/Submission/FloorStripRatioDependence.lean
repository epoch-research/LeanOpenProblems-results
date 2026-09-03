import Submission.PrimePowerError

/-! The additive unit-width floor strip is not a function only of the ratio
of its two integer arguments. A single Mellin window needs further scale data. -/
namespace Erdos972FloorStripRatioDependence

open Erdos972PrimePowerError
set_option maxHeartbeats 500000

/-- A dilation preserves the ratio but can leave the unit-width strip. -/
theorem exists_same_ratio_different_floor_status {α : ℝ} (hα : 1 < α)
    (hI : Irrational α) :
    ∃ q c : ℕ, 0 < q ∧ 0 < c ∧ q = floorMul α 1 ∧
      c*q ≠ floorMul α c ∧ (c*q : ℕ)/(c : ℝ) = (q : ℝ) := by
  let q := ⌊α⌋₊
  have hq : 0 < q := Nat.floor_pos.mpr hα.le
  have hne : α ≠ (q : ℝ) := by
    intro he
    apply hI
    exact ⟨(q : ℚ), by simpa using he.symm⟩
  have hfrac : 0 < α-(q : ℝ) := sub_pos.mpr
    (lt_of_le_of_ne (Nat.floor_le (show 0 ≤ α by linarith)) hne.symm)
  obtain ⟨c, hc⟩ := exists_nat_gt (1/(α-(q : ℝ)))
  have hcR : (0 : ℝ) < c := (one_div_pos.mpr hfrac).trans hc
  have hc0 : 0 < c := Nat.cast_pos.mp hcR
  have hprod : 1 < (c : ℝ)*(α-(q : ℝ)) := (div_lt_iff₀ hfrac).mp hc
  have hbound : c*q+1 ≤ floorMul α c := by
    apply Nat.le_floor
    push_cast
    nlinarith only [hprod]
  refine ⟨q, c, hq, hc0, ?_, by omega, ?_⟩
  · simp only [floorMul, Nat.cast_one, mul_one, q]
  · push_cast
    field_simp

/-- In particular, no one-variable ratio kernel can exactly represent all
of the sharp floor incidences at a fixed irrational slope. This does not
rule out a scale-dependent or higher-dimensional Mellin representation. -/
theorem no_ratio_only_floor_kernel {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    ¬ ∃ K : ℝ → ℝ, ∀ n q : ℕ, 0 < n → 0 < q →
      K ((q : ℝ)/n) = if q = floorMul α n then 1 else 0 := by
  rintro ⟨K, hK⟩
  obtain ⟨q, c, hq, hc, he, hne, hratio⟩ := exists_same_ratio_different_floor_status hα hI
  have h₁ := hK 1 q (by omega) hq
  have h₂ := hK c (c*q) hc (Nat.mul_pos hc hq)
  simp only [Nat.cast_one, div_one, if_pos he] at h₁
  rw [hratio, if_neg hne, h₁] at h₂
  norm_num at h₂

#print axioms exists_same_ratio_different_floor_status
#print axioms no_ratio_only_floor_kernel

end Erdos972FloorStripRatioDependence
