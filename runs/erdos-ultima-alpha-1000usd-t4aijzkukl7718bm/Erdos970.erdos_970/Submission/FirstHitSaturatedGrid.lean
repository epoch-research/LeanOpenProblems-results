import Submission.FirstHitGrid
import Submission.FirstHitLowerCutoff

/-! A twenty-four-bin reciprocal envelope beginning at 29/50. The Euler
reciprocal is bounded below using the coefficient 9/5. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def saturatedHitNode : ℕ → ℝ
  | 0 => 29 / 50
  | j + 1 => firstHitNode j
noncomputable def saturatedHitNodeUpper : ℕ → ℝ
  | 0 => 50 / 29
  | j + 1 => firstHitNodeUpper j
noncomputable def saturatedHitSlope (j : ℕ) : ℝ :=
  (saturatedHitNodeUpper (j + 1) - saturatedHitNodeUpper j) /
    (saturatedHitNode (j + 1) - saturatedHitNode j)
noncomputable def saturatedHitIntercept (j : ℕ) : ℝ :=
  saturatedHitNodeUpper j - saturatedHitSlope j * saturatedHitNode j
noncomputable def saturatedHitExcessIntercept (j : ℕ) : ℝ :=
  (10001 / 10000 : ℝ) * saturatedHitIntercept j - 5 / 9
noncomputable def saturatedHitExcessSlope (j : ℕ) : ℝ :=
  (10001 / 10000 : ℝ) * saturatedHitSlope j

lemma saturatedHitNode_step_pos (j : ℕ) : saturatedHitNode j < saturatedHitNode (j + 1) := by
  cases j with
  | zero => norm_num [saturatedHitNode, firstHitNode]
  | succ j => simpa only [saturatedHitNode] using
      (show firstHitNode j < firstHitNode (j + 1) by linarith [firstHitNode_step j])

lemma saturatedHitNode_monotone : Monotone saturatedHitNode :=
  (strictMono_nat_of_lt_succ saturatedHitNode_step_pos).monotone

lemma saturatedHitNode_nonneg (j : ℕ) : 0 ≤ saturatedHitNode j := by
  have hh : (29 / 50 : ℝ) ≤ saturatedHitNode j := saturatedHitNode_monotone (Nat.zero_le j)
  linarith

lemma saturatedHitNode_mem (j : ℕ) (hj : j ≤ 24) :
    saturatedHitNode j ∈ Set.Icc (29 / 50 : ℝ) 3 := by
  cases j with
  | zero => norm_num [saturatedHitNode]
  | succ j =>
    have hh := firstHitNode_mem j (by omega)
    exact ⟨(by norm_num : (29 / 50 : ℝ) ≤ 7 / 10).trans hh.1, hh.2⟩

lemma saturatedHitNode_upper (j : ℕ) (hj : j ≤ 24) :
    1 / firstHitFullProfile (saturatedHitNode j) ≤ saturatedHitNodeUpper j := by
  cases j with
  | zero => norm_num [saturatedHitNode, saturatedHitNodeUpper, firstHitFullProfile]
  | succ j => exact firstHitNode_upper j (by omega)

lemma saturated_fullReciprocal_convex_on_bin (j : ℕ) (hj : j < 24) :
    ConvexOn ℝ (Set.Icc (saturatedHitNode j) (saturatedHitNode (j + 1)))
      (fun u => 1 / firstHitFullProfile u) := by
  cases j with
  | zero =>
    have hi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun u : ℝ => 1 / u) := by
      simpa only [zpow_neg_one, one_div] using
        (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
    have hs : Set.Icc (saturatedHitNode 0) (saturatedHitNode 1) ⊆ Set.Ioi (0 : ℝ) := by
      intro u hu
      norm_num [saturatedHitNode, firstHitNode] at hu ⊢
      linarith [hu.1]
    apply (hi.subset hs (convex_Icc _ _)).congr
    intro u hu
    have hu1 : u ≤ 1 := by
      have hh := hu.2
      norm_num [saturatedHitNode, firstHitNode] at hh
      linarith
    simp only [firstHitFullProfile, if_pos hu1]
  | succ j => exact fullReciprocal_convex_on_bin j (by omega)

lemma saturatedHit_chord_upper (j : ℕ) (hj : j < 24) (u : ℝ)
    (hu : u ∈ Set.Icc (saturatedHitNode j) (saturatedHitNode (j + 1))) :
    1 / firstHitFullProfile u ≤ saturatedHitIntercept j + saturatedHitSlope j * u := by
  have hh := convex_le_endpoint_chord (saturatedHitNode_step_pos j)
    (saturated_fullReciprocal_convex_on_bin j hj) hu
    (saturatedHitNode_upper j (by omega)) (saturatedHitNode_upper (j + 1) (by omega))
  convert hh using 1
  unfold saturatedHitIntercept saturatedHitSlope
  have hd := (sub_pos.mpr (saturatedHitNode_step_pos j)).ne'
  field_simp
  <;> ring

lemma saturatedHit_excess_chord_budget :
    (∑ j ∈ range 24, (saturatedHitNode (j + 1) - saturatedHitNode j) *
      (2 * saturatedHitExcessIntercept j + saturatedHitExcessSlope j *
        (saturatedHitNode j + saturatedHitNode (j + 1)))) ≤ 109 / 100 := by
  norm_num [sum_range_succ, saturatedHitNode, saturatedHitExcessIntercept, saturatedHitExcessSlope,
    saturatedHitIntercept, saturatedHitSlope, saturatedHitNodeUpper,
    firstHitNode, firstHitNodeUpper, firstHitGridUpper]

noncomputable def saturatedHitChordError : ℝ := (WeightedMertens.boundConstant + 1) *
  ∑ j ∈ range 24,
    (2 * |saturatedHitExcessIntercept j - saturatedHitExcessSlope j / 2| *
      (2 * saturatedHitNode (j + 1) + 1) ^ 2 +
      |saturatedHitExcessSlope j| * (2 * saturatedHitNode (j + 1) + 1) ^ 3)

theorem saturatedHit_affine_prime_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L) :
    (∑ j ∈ range 24, WeightedMertens.affineRatioPrimeInterval L
      (saturatedHitExcessIntercept j) (saturatedHitExcessSlope j)
      (exp (L / (2 * saturatedHitNode (j + 1) + 1)))
      (exp (L / (2 * saturatedHitNode j + 1)))) ≤
      (109 / 100) / L + saturatedHitChordError / L ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ range 24) :=
    WeightedMertens.affineRatioPrimeInterval_scaled_error L (saturatedHitExcessIntercept j)
      (saturatedHitExcessSlope j) (saturatedHitNode j) (saturatedHitNode (j + 1)) hL
      (saturatedHitNode_nonneg j) (saturatedHitNode_step_pos j).le
      (by
        have hh := (saturatedHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).2
        have hlog := log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith only [hh, hsmall, hlog])
  have hh := sum_le_sum (fun j hj => (abs_le.mp (hb j hj)).2)
  simp only [sum_sub_distrib, ← mul_sum, ← sum_div] at hh
  have hbudget := div_le_div_of_nonneg_right saturatedHit_excess_chord_budget hL.le
  unfold saturatedHitChordError
  linear_combination hh + hbudget

#print axioms saturatedHit_chord_upper
#print axioms saturatedHit_affine_prime_sum_le
end Erdos970.FiniteSelberg
