import Submission.RetainedRealCompression

/-! Exact retained mass caps every coordinate marginal. The resulting
positive-mixture coefficients remain ordered as the retained mass varies.
These are auxiliary comparisons, not a solution of the odd covering problem. -/
namespace Erdos7CappedFiberMixture
open scoped BigOperators
open Erdos7RealChain Erdos7RetainedRealCompression
set_option maxHeartbeats 1500000

lemma min_difference_identity (h a b : ℝ) (hba : b ≤ a) :
    min h a - min h b = min (max (h-b) 0) (a-b) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

lemma min_difference_monotone (a b : ℝ) (hba : b ≤ a) :
    Monotone (fun h : ℝ => min h a - min h b) := by
  intro h k hhk
  dsimp only
  rw [min_difference_identity h a b hba, min_difference_identity k a b hba]
  exact min_le_min (max_le_max (by linarith) le_rfl) le_rfl

lemma baseline_monotone (a : ℝ) : Monotone (fun h : ℝ => h-min h a) := by
  have he (h : ℝ) : h-min h a = max (h-a) 0 := by
    simp only [min_def, max_def]
    split_ifs <;> linarith
  intro h k hhk
  dsimp only
  rw [he, he]
  exact max_le_max (by linarith) le_rfl

lemma capped_coefficients_ordered {α : Type*} [Preorder α]
    (h : α → ℝ) (hh : Antitone h) (q : ℕ → ℝ)
    (hq : ∀ j, q (j+1) ≤ q j) :
    Antitone (fun k => h k-min (h k) (q 0)) ∧
    ∀ j, Antitone (fun k => min (h k) (q j)-min (h k) (q (j+1))) := by
  refine ⟨(baseline_monotone (q 0)).comp_antitone hh, ?_⟩
  intro j
  exact (min_difference_monotone (q j) (q (j+1)) (hq j)).comp_antitone hh

lemma capped_coefficient_nonneg (h : ℝ) (q : ℕ → ℝ)
    (hq : ∀ j, q (j+1) ≤ q j) :
    0 ≤ h-min h (q 0) ∧ ∀ j, 0 ≤ min h (q j)-min h (q (j+1)) := by
  exact ⟨sub_nonneg.mpr (min_le_left _ _),
    fun j => sub_nonneg.mpr (min_le_min le_rfl (hq j))⟩

lemma capped_coefficients_mass (h : ℝ) (hh : 0 ≤ h) (q : ℕ → ℝ)
    (R : ℕ) (hqR : q R=0) :
    (h-min h (q 0)) + ∑ j ∈ Finset.range R,
      (min h (q j)-min h (q (j+1))) = h := by
  rw [Finset.sum_range_sub', hqR, min_eq_right hh]
  ring

/-- The bound by the total fiber mass is independent of the event-density
bound and can therefore be combined with it before convex compression. -/
lemma capped_group_marginal {Ω : Type*} [Fintype Ω]
    (ν s : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x) (m h W q : ℝ)
    (hmass : (∑ x, ν x) = m*h) (hsW : ∀ x, s x ≤ W)
    (hmarg : (∑ x, ν x*s x) ≤ m*q*W) :
    (∑ x, ν x*s x) ≤ m*(min h q)*W := by
  have hb : (∑ x, ν x*s x) ≤ m*h*W := by
    calc
      _ ≤ ∑ x, ν x*W := Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (hsW x) (hν x))
      _ = _ := by rw [← Finset.sum_mul, hmass]
  by_cases hhq : h ≤ q
  · simpa only [min_eq_left hhq] using hb
  · simpa only [min_eq_right (le_of_not_ge hhq)] using hmarg

/-- This positive retained mixture is valid without assuming h >= q(0).
For a geometric marginal profile it is the upper-h-mass refinement, and
all its coefficients are ordered functions of h. -/
theorem retained_capped_group_mixture {Ω : Type*} [Fintype Ω]
    (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x) (m h : ℝ) (hh : 0 ≤ h)
    (hmass : (∑ x, ν x) = m*h)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ)
    (a : ℝ) (W : ℕ → ℝ) (s : ℕ → Ω → ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hW : ∀ j<R, 0 ≤ W j) (hs : ∀ j<R, ∀ x, 0 ≤ s j x)
    (hsW : ∀ j<R, ∀ x, s j x ≤ W j)
    (hmarg : ∀ j<R, (∑ x, ν x*s j x) ≤ m*q j*W j) (hqR : q R=0) :
    (∑ x, ν x*φ (a + prefixWeight (fun j => s j x) R)) ≤
      m*((h-min h (q 0))*φ a + ∑ j ∈ Finset.range R,
        (min h (q j)-min h (q (j+1)))*φ (a+prefixWeight W (j+1))) := by
  apply retained_group_mixture ν hν m h hmass φ hφ hmφ a W s
    (fun j => min h (q j)) R hW hs hsW
  · intro j hj
    exact capped_group_marginal ν (s j) hν m h (W j) (q j) hmass
      (hsW j hj) (hmarg j hj)
  · rw [hqR, min_eq_right hh]

#print axioms capped_coefficients_ordered
#print axioms capped_coefficients_mass
#print axioms retained_capped_group_mixture
end Erdos7CappedFiberMixture
