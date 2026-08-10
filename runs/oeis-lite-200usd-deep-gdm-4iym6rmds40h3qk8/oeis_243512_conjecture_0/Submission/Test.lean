import FormalConjectures.Util.ProblemImports
import Submission.Spec

theorem a_ne_zero_iff (n : ℕ) : a n ≠ 0 ↔ ∃ i, 0 < i ∧ A243473_val i = n := by
  constructor
  · intro h
    by_contra h_empty
    have h_empty_set : {i : ℕ | 0 < i ∧ A243473_val i = n} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact h_empty ⟨x, hx⟩
    have ha : a n = 0 := by
      dsimp [a]
      rw [h_empty_set, Nat.sInf_empty]
    exact h ha
  · rintro ⟨i, hi_gt, hi_val⟩
    have h_nonempty : {i : ℕ | 0 < i ∧ A243473_val i = n}.Nonempty := ⟨i, hi_gt, hi_val⟩
    have h_mem : a n ∈ {i : ℕ | 0 < i ∧ A243473_val i = n} := by
      dsimp [a]
      exact Nat.sInf_mem h_nonempty
    exact Ne.symm (ne_of_lt h_mem.1)

