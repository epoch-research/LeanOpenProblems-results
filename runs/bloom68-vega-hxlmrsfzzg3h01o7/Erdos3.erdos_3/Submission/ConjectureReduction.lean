import Submission.Uniformity

/-!
# Exact finite reformulation of Erdős Problem 3

This file does not import or use either sorry-bearing declaration in `Spec.lean`.
It proves a logical equivalence with uniform finite weighted bounds, not those
bounds themselves.
-/

namespace Erdos3Weighted

open Filter

/-- The proposition from the specification, repeated without referencing its theorem. -/
def Conjecture : Prop :=
  ∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
    ∃ᶠ k : ℕ in atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)

/-- The original conjecture is equivalent to a uniform bound, for each fixed
length at least three, on all finite AP-free reciprocal sums. -/
theorem conjecture_iff_uniformBounds :
    Conjecture ↔ ∀ k : ℕ, 3 ≤ k → UniformBound k := by
  constructor
  · intro h k hk
    apply uniformBound_of_all_summable hk
    intro A hA
    by_contra hnot
    obtain ⟨S, hSA, hS⟩ :=
      (Erdos3Reduction.frequently_isAPOfLength_iff_forall A).mp (h A hnot) k
    exact hA S hSA hS
  · exact erdos3_of_uniformBounds

/-- A disproof is equivalently an unbounded family of finite reciprocal sums
avoiding one fixed length, which may be chosen at least three. -/
theorem not_conjecture_iff :
    ¬ Conjecture ↔ ∃ k : ℕ, 3 ≤ k ∧ ¬ UniformBound k := by
  rw [conjecture_iff_uniformBounds]
  simp only [not_forall, exists_prop]

/-- The length-two weighted bound is elementary: a set excluding a two-term AP
contains at most one point. -/
theorem uniformBound_two : UniformBound 2 := by
  classical
  refine ⟨1, ?_⟩
  intro F hF
  have hcard : F.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with hab | hba
    · apply hF {a, b} _ (Nat.isAPOfLength_pair hab)
      intro n hn
      rcases hn with rfl | hn
      · exact ha
      · exact hn ▸ hb
    · apply hF {b, a} _ (Nat.isAPOfLength_pair hba)
      intro n hn
      rcases hn with rfl | hn
      · exact hb
      · exact hn ▸ ha
  calc
    weight F ≤ ∑ _ ∈ F, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n = 0
      · simp [hn]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        simpa only [div_one] using one_div_le_one_div_of_le (by norm_num) hn1
    _ = (F.card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcard

end Erdos3Weighted

#print axioms Erdos3Weighted.conjecture_iff_uniformBounds
#print axioms Erdos3Weighted.not_conjecture_iff
#print axioms Erdos3Weighted.uniformBound_two
