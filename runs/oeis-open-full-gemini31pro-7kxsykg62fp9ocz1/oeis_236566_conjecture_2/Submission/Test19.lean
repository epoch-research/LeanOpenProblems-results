import Mathlib
import Submission.Spec

set_option maxRecDepth 2000000

lemma lemoine_of_part_ii (h : a236566_conjecture_part_ii) : lemoine_conjecture := by
  intro k hk_odd hk_gt
  by_cases hk_61 : k > 61
  · obtain ⟨n, hn⟩ : ∃ n, k = 2 * n + 1 := by
      use k / 2
      have : 2 ∣ k - 1 := by
        rcases hk_odd with ⟨m, hm⟩
        rw [hm]
        omega
      omega
    have hn30 : n > 30 := by omega
    obtain ⟨p, q, hp, hq, _, heq⟩ := h n hn30
    use q, p
    refine ⟨hq, hp, ?_⟩
    omega
  · have : ∀ k < 62, Odd k → 5 < k → ∃ p < k, ∃ q < k, Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
      decide
    rcases this k (by omega) hk_odd hk_gt with ⟨p, _, q, _, hp, hq, heq⟩
    exact ⟨p, q, hp, hq, heq⟩
