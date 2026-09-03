import Submission.FirstHitGrid
import Submission.FirstHitExtendedCutoff

/-! A twenty-four-bin reciprocal envelope beginning at 63/100. The Euler
reciprocal is bounded below using the coefficient 9/5. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def refinedHitNode : ℕ → ℝ
  | 0 => 63 / 100
  | j + 1 => firstHitNode j
noncomputable def refinedHitNodeUpper : ℕ → ℝ
  | 0 => 100 / 63
  | j + 1 => firstHitNodeUpper j
noncomputable def refinedHitSlope (j : ℕ) : ℝ :=
  (refinedHitNodeUpper (j + 1) - refinedHitNodeUpper j) /
    (refinedHitNode (j + 1) - refinedHitNode j)
noncomputable def refinedHitIntercept (j : ℕ) : ℝ :=
  refinedHitNodeUpper j - refinedHitSlope j * refinedHitNode j
noncomputable def refinedHitExcessIntercept (j : ℕ) : ℝ :=
  (10001 / 10000 : ℝ) * refinedHitIntercept j - 5 / 9
noncomputable def refinedHitExcessSlope (j : ℕ) : ℝ :=
  (10001 / 10000 : ℝ) * refinedHitSlope j

lemma refinedHitNode_step_pos (j : ℕ) : refinedHitNode j < refinedHitNode (j + 1) := by
  cases j with
  | zero => norm_num [refinedHitNode, firstHitNode]
  | succ j => simpa only [refinedHitNode] using
      (show firstHitNode j < firstHitNode (j + 1) by linarith [firstHitNode_step j])

lemma refinedHitNode_monotone : Monotone refinedHitNode :=
  (strictMono_nat_of_lt_succ refinedHitNode_step_pos).monotone

lemma refinedHitNode_nonneg (j : ℕ) : 0 ≤ refinedHitNode j := by
  have hh : (63 / 100 : ℝ) ≤ refinedHitNode j := refinedHitNode_monotone (Nat.zero_le j)
  linarith

lemma refinedHitNode_mem (j : ℕ) (hj : j ≤ 24) :
    refinedHitNode j ∈ Set.Icc (63 / 100 : ℝ) 3 := by
  cases j with
  | zero => norm_num [refinedHitNode]
  | succ j =>
    have hh := firstHitNode_mem j (by omega)
    exact ⟨(by norm_num : (63 / 100 : ℝ) ≤ 7 / 10).trans hh.1, hh.2⟩

lemma refinedHitNode_upper (j : ℕ) (hj : j ≤ 24) :
    1 / firstHitFullProfile (refinedHitNode j) ≤ refinedHitNodeUpper j := by
  cases j with
  | zero => norm_num [refinedHitNode, refinedHitNodeUpper, firstHitFullProfile]
  | succ j => exact firstHitNode_upper j (by omega)

lemma refined_fullReciprocal_convex_on_bin (j : ℕ) (hj : j < 24) :
    ConvexOn ℝ (Set.Icc (refinedHitNode j) (refinedHitNode (j + 1)))
      (fun u => 1 / firstHitFullProfile u) := by
  cases j with
  | zero =>
    have hi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun u : ℝ => 1 / u) := by
      simpa only [zpow_neg_one, one_div] using
        (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
    have hs : Set.Icc (refinedHitNode 0) (refinedHitNode 1) ⊆ Set.Ioi (0 : ℝ) := by
      intro u hu
      norm_num [refinedHitNode, firstHitNode] at hu ⊢
      linarith [hu.1]
    apply (hi.subset hs (convex_Icc _ _)).congr
    intro u hu
    have hu1 : u ≤ 1 := by
      have hh := hu.2
      norm_num [refinedHitNode, firstHitNode] at hh
      linarith
    simp only [firstHitFullProfile, if_pos hu1]
  | succ j => exact fullReciprocal_convex_on_bin j (by omega)

lemma refinedHit_chord_upper (j : ℕ) (hj : j < 24) (u : ℝ)
    (hu : u ∈ Set.Icc (refinedHitNode j) (refinedHitNode (j + 1))) :
    1 / firstHitFullProfile u ≤ refinedHitIntercept j + refinedHitSlope j * u := by
  have hh := convex_le_endpoint_chord (refinedHitNode_step_pos j)
    (refined_fullReciprocal_convex_on_bin j hj) hu
    (refinedHitNode_upper j (by omega)) (refinedHitNode_upper (j + 1) (by omega))
  convert hh using 1
  unfold refinedHitIntercept refinedHitSlope
  have hd := (sub_pos.mpr (refinedHitNode_step_pos j)).ne'
  field_simp
  <;> ring

lemma refinedHit_excess_chord_budget :
    (∑ j ∈ range 24, (refinedHitNode (j + 1) - refinedHitNode j) *
      (2 * refinedHitExcessIntercept j + refinedHitExcessSlope j *
        (refinedHitNode j + refinedHitNode (j + 1)))) ≤ 35213 / 36000 := by
  norm_num [sum_range_succ, refinedHitNode, refinedHitExcessIntercept, refinedHitExcessSlope,
    refinedHitIntercept, refinedHitSlope, refinedHitNodeUpper,
    firstHitNode, firstHitNodeUpper, firstHitGridUpper]

noncomputable def refinedHitChordError : ℝ := (WeightedMertens.boundConstant + 1) *
  ∑ j ∈ range 24,
    (2 * |refinedHitExcessIntercept j - refinedHitExcessSlope j / 2| *
      (2 * refinedHitNode (j + 1) + 1) ^ 2 +
      |refinedHitExcessSlope j| * (2 * refinedHitNode (j + 1) + 1) ^ 3)

theorem refinedHit_affine_prime_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L) :
    (∑ j ∈ range 24, WeightedMertens.affineRatioPrimeInterval L
      (refinedHitExcessIntercept j) (refinedHitExcessSlope j)
      (exp (L / (2 * refinedHitNode (j + 1) + 1)))
      (exp (L / (2 * refinedHitNode j + 1)))) ≤
      (35213 / 36000) / L + refinedHitChordError / L ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ range 24) :=
    WeightedMertens.affineRatioPrimeInterval_scaled_error L (refinedHitExcessIntercept j)
      (refinedHitExcessSlope j) (refinedHitNode j) (refinedHitNode (j + 1)) hL
      (refinedHitNode_nonneg j) (refinedHitNode_step_pos j).le
      (by
        have hh := (refinedHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).2
        have hlog := log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith only [hh, hsmall, hlog])
  have hh := sum_le_sum (fun j hj => (abs_le.mp (hb j hj)).2)
  simp only [sum_sub_distrib, ← mul_sum, ← sum_div] at hh
  have hbudget := div_le_div_of_nonneg_right refinedHit_excess_chord_budget hL.le
  unfold refinedHitChordError
  linear_combination hh + hbudget

#print axioms refinedHit_chord_upper
#print axioms refinedHit_affine_prime_sum_le
end Erdos970.FiniteSelberg
