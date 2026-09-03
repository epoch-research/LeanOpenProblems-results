import Submission.FirstHitIntegerCutoff
import Submission.PrimeAffineRatio

/-! A rational affine upper envelope for the first-hit reciprocal profile.
The main-term budget and the finite prime-sum error are retained separately. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def firstHitNode (j : ℕ) : ℝ := ((j : ℝ) + 7) / 10
noncomputable def firstHitNodeUpper (j : ℕ) : ℝ :=
  if j < 3 then 10 / ((j : ℝ) + 7) else firstHitGridUpper (j - 3)
noncomputable def firstHitSlope (j : ℕ) : ℝ := 10 * (firstHitNodeUpper (j + 1) - firstHitNodeUpper j)
noncomputable def firstHitIntercept (j : ℕ) : ℝ := firstHitNodeUpper j - firstHitSlope j * firstHitNode j
noncomputable def firstHitExcessIntercept (j : ℕ) : ℝ := (10001 / 10000 : ℝ) * firstHitIntercept j - 10 / 19
noncomputable def firstHitExcessSlope (j : ℕ) : ℝ := (10001 / 10000 : ℝ) * firstHitSlope j

lemma firstHitNode_step (j : ℕ) : firstHitNode (j + 1) - firstHitNode j = 1 / 10 := by
  unfold firstHitNode
  push_cast
  ring

lemma firstHitNode_mem (j : ℕ) (hj : j ≤ 23) : firstHitNode j ∈ Set.Icc (7 / 10 : ℝ) 3 := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj23 : (j : ℝ) ≤ 23 := by exact_mod_cast hj
  unfold firstHitNode
  constructor <;> linarith

lemma fullProfile_eq_profile (u : ℝ) (hu : 1 ≤ u) : firstHitFullProfile u = firstHitProfile u := by
  unfold firstHitFullProfile
  split_ifs with hu1
  · have he : u = 1 := by linarith
    subst u
    norm_num [firstHitProfile]
  · rfl

lemma firstHitNode_upper (j : ℕ) (hj : j ≤ 23) :
    1 / firstHitFullProfile (firstHitNode j) ≤ firstHitNodeUpper j := by
  by_cases hj3 : j ≤ 3
  · interval_cases j <;> norm_num [firstHitFullProfile, firstHitNode, firstHitNodeUpper, firstHitGridUpper]
  · have hsub : 3 ≤ j := by omega
    have hnode : firstHitNode j = 1 + ((j - 3 : ℕ) : ℝ) / 10 := by
      rw [Nat.cast_sub hsub]
      unfold firstHitNode
      ring
    have hge : 1 ≤ firstHitNode j := by
      have hh : (3 : ℝ) ≤ j := by exact_mod_cast hsub
      unfold firstHitNode
      linarith
    rw [fullProfile_eq_profile _ hge, hnode]
    simpa only [firstHitNodeUpper, if_neg (show ¬j < 3 by omega)] using
      firstHitReciprocal_grid_bound (j - 3) (by omega)

lemma fullReciprocal_convex_on_bin (j : ℕ) (hj : j < 23) :
    ConvexOn ℝ (Set.Icc (firstHitNode j) (firstHitNode (j + 1)))
      (fun u => 1 / firstHitFullProfile u) := by
  by_cases hj3 : j < 3
  · have hi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun u : ℝ => 1 / u) := by
      simpa only [zpow_neg_one, one_div] using
        (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn
    have hsub : Set.Icc (firstHitNode j) (firstHitNode (j + 1)) ⊆ Set.Ioi (0 : ℝ) := by
      intro u hu
      have hh := (firstHitNode_mem j (by omega)).1
      exact lt_of_lt_of_le (by linarith : 0 < firstHitNode j) hu.1
    apply (hi.subset hsub (convex_Icc _ _)).congr
    intro u hu
    have hjr : (j : ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by omega)
    have hu1 : u ≤ 1 := by
      have hh := hu.2
      unfold firstHitNode at hh
      push_cast at hh
      linarith
    simp only [firstHitFullProfile, if_pos hu1]
  · have hsub : Set.Icc (firstHitNode j) (firstHitNode (j + 1)) ⊆ Set.Icc (1 : ℝ) 3 := by
      intro u hu
      have hjr : (3 : ℝ) ≤ j := by exact_mod_cast (show 3 ≤ j by omega)
      have hlow : 1 ≤ firstHitNode j := by unfold firstHitNode; linarith
      exact ⟨hlow.trans hu.1, hu.2.trans (firstHitNode_mem (j + 1) (by omega)).2⟩
    apply (firstHitReciprocal_convex.subset hsub (convex_Icc _ _)).congr
    intro u hu
    dsimp only
    rw [fullProfile_eq_profile u (hsub hu).1]
    rfl

lemma convex_le_endpoint_chord {f : ℝ → ℝ} {a b u A B : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hu : u ∈ Set.Icc a b) (hA : f a ≤ A) (hB : f b ≤ B) :
    f u ≤ (b - u) / (b - a) * A + (u - a) / (b - a) * B := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have h1 : 0 ≤ (b - u) / (b - a) := div_nonneg (sub_nonneg.mpr hu.2) hd.le
  have h2 : 0 ≤ (u - a) / (b - a) := div_nonneg (sub_nonneg.mpr hu.1) hd.le
  have hs : (b - u) / (b - a) + (u - a) / (b - a) = 1 := by field_simp; ring
  have he : (b - u) / (b - a) * a + (u - a) / (b - a) * b = u := by field_simp; ring
  have hh := hf.2 (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩) h1 h2 hs
  simp only [smul_eq_mul, he] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hA h1) (mul_le_mul_of_nonneg_left hB h2))

lemma firstHit_chord_upper (j : ℕ) (hj : j < 23) (u : ℝ)
    (hu : u ∈ Set.Icc (firstHitNode j) (firstHitNode (j + 1))) :
    1 / firstHitFullProfile u ≤ firstHitIntercept j + firstHitSlope j * u := by
  have hh := convex_le_endpoint_chord
    (show firstHitNode j < firstHitNode (j + 1) by linarith [firstHitNode_step j])
    (fullReciprocal_convex_on_bin j hj) hu
    (firstHitNode_upper j (by omega)) (firstHitNode_upper (j + 1) (by omega))
  rw [firstHitNode_step] at hh
  have hstep : firstHitNode (j + 1) = firstHitNode j + 1 / 10 := by linarith [firstHitNode_step j]
  rw [hstep] at hh
  unfold firstHitIntercept firstHitSlope
  convert hh using 1 <;> ring

/-- This is the exact finite rational trapezoidal budget, not a numerical
quadrature assumption. -/
lemma firstHit_chord_budget :
    (∑ j ∈ range 23, (firstHitNode (j + 1) - firstHitNode j) *
      (2 * firstHitIntercept j + firstHitSlope j * (firstHitNode j + firstHitNode (j + 1)))) ≤ 17 / 5 := by
  norm_num [sum_range_succ, firstHitNode, firstHitIntercept, firstHitSlope, firstHitNodeUpper, firstHitGridUpper]

lemma firstHit_excess_chord_budget :
    (∑ j ∈ range 23, (firstHitNode (j + 1) - firstHitNode j) *
      (2 * firstHitExcessIntercept j + firstHitExcessSlope j * (firstHitNode j + firstHitNode (j + 1)))) ≤
      93 / 95 + 17 / 50000 := by
  norm_num [sum_range_succ, firstHitNode, firstHitExcessIntercept, firstHitExcessSlope,
    firstHitIntercept, firstHitSlope, firstHitNodeUpper, firstHitGridUpper]

noncomputable def firstHitChordError : ℝ := (WeightedMertens.boundConstant + 1) *
  ∑ j ∈ range 23,
    (2 * |firstHitExcessIntercept j - firstHitExcessSlope j / 2| * (2 * firstHitNode (j + 1) + 1) ^ 2 +
      |firstHitExcessSlope j| * (2 * firstHitNode (j + 1) + 1) ^ 3)

/-- The sum of all affine prime-bin upper bounds, including their common
O(1/L^2) error. -/
theorem firstHit_affine_prime_sum_le (L : ℝ) (hL : 0 < L) (hsmall : 7 * log 2 ≤ L) :
    (∑ j ∈ range 23, WeightedMertens.affineRatioPrimeInterval L
      (firstHitExcessIntercept j) (firstHitExcessSlope j)
      (exp (L / (2 * firstHitNode (j + 1) + 1))) (exp (L / (2 * firstHitNode j + 1)))) ≤
      (93 / 95 + 17 / 50000) / L + firstHitChordError / L ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ range 23) :=
    WeightedMertens.affineRatioPrimeInterval_scaled_error L (firstHitExcessIntercept j)
      (firstHitExcessSlope j) (firstHitNode j) (firstHitNode (j + 1)) hL
      (by have := (firstHitNode_mem j (by have := mem_range.mp hj; omega)).1; linarith)
      (by linarith [firstHitNode_step j])
      (by
        have hh := (firstHitNode_mem (j + 1) (by have := mem_range.mp hj; omega)).2
        have hlog := log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith only [hh, hsmall, hlog])
  have hh := sum_le_sum (fun j hj => (abs_le.mp (hb j hj)).2)
  simp only [sum_sub_distrib, ← mul_sum, ← sum_div] at hh
  have hbudget := div_le_div_of_nonneg_right firstHit_excess_chord_budget hL.le
  unfold firstHitChordError
  linear_combination hh + hbudget

#print axioms firstHit_chord_upper
#print axioms firstHit_affine_prime_sum_le
end Erdos970.FiniteSelberg
