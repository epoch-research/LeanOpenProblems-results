import FormalConjecturesUtil

/-!
Positive pointwise scaling of every test cost does not affect the feasibility
of strictly negative expectations when the full simplex of weights is free.
This is an auxiliary finite-dimensional fact, not an arithmetic covering result.
-/

namespace Erdos7RetentionTilt

open scoped BigOperators

variable {I J : Type*} [Fintype I]

def Simplex (w : I → ℚ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

def mass (w h : I → ℚ) : ℚ := ∑ i, w i * h i

def tilt (w h : I → ℚ) (i : I) : ℚ := w i * h i / mass w h

lemma mass_pos {w h : I → ℚ} (hw : Simplex w) (hh : ∀ i, 0 < h i) :
    0 < mass w h := by
  have hwpos : 0 < ∑ i, w i := by rw [hw.2]; norm_num
  obtain ⟨i, hi, hwi⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun i _ => hw.1 i)).mp hwpos
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw.1 i) (hh i).le)
    ⟨i, hi, mul_pos hwi (hh i)⟩

lemma tilt_simplex {w h : I → ℚ} (hw : Simplex w) (hh : ∀ i, 0 < h i) :
    Simplex (tilt w h) := by
  have hz := mass_pos hw hh
  refine ⟨fun i => div_nonneg (mul_nonneg (hw.1 i) (hh i).le) hz.le, ?_⟩
  simp only [tilt, ← Finset.sum_div]
  exact div_self hz.ne'

lemma tilt_cost (w h a : I → ℚ) :
    (∑ i, tilt w h i * a i) = (∑ i, w i * h i * a i) / mass w h := by
  simp only [tilt, div_mul_eq_mul_div, Finset.sum_div]

/-- Only positive common point factors are absorbed; no restriction on weights
other than membership in the full simplex is permitted in this equivalence. -/
theorem feasible_iff (a : J → I → ℚ) (h : I → ℚ) (hh : ∀ i, 0 < h i) :
    (∃ w : I → ℚ, Simplex w ∧ ∀ j, (∑ i, w i * h i * a j i) < 0) ↔
    (∃ w : I → ℚ, Simplex w ∧ ∀ j, (∑ i, w i * a j i) < 0) := by
  constructor
  · rintro ⟨w, hw, ha⟩
    refine ⟨tilt w h, tilt_simplex hw hh, fun j => ?_⟩
    rw [tilt_cost]
    exact div_neg_of_neg_of_pos (ha j) (mass_pos hw hh)
  · rintro ⟨w, hw, ha⟩
    have hi : ∀ i, 0 < (h i)⁻¹ := fun i => inv_pos.mpr (hh i)
    refine ⟨tilt w (fun i => (h i)⁻¹), tilt_simplex hw hi, fun j => ?_⟩
    have heq : (∑ i, tilt w (fun i => (h i)⁻¹) i * h i * a j i) =
        (∑ i, w i * a j i) / mass w (fun i => (h i)⁻¹) := by
      simp only [mul_assoc]
      rw [tilt_cost]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [← mul_assoc]
      rw [mul_assoc (w i) ((h i)⁻¹) (h i), inv_mul_cancel₀ (hh i).ne', mul_one]
    rw [heq]
    exact div_neg_of_neg_of_pos (ha j) (mass_pos hw hi)

#print axioms feasible_iff

end Erdos7RetentionTilt
