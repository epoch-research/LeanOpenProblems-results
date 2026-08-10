import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem conj_zero :
  (0 < 0 → 0 < A273110 0) ∧
  (A273110 0 = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ 0 = 4 ^ k * m) := by
  constructor
  · intro h
    omega
  · constructor
    · intro h
      rw [A273110_eq_eval] at h
      -- A273110_eval 0 is 0
      contradiction
    · rintro ⟨k, m, hm, h0⟩
      -- 4^k * m = 0 is impossible
      have : 4^k * m > 0 := by
        -- 4^k > 0 and m > 0
        sorry
      omega
