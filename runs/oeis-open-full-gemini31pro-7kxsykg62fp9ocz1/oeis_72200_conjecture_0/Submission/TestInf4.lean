import FormalConjectures.Util.ProblemImports
open Set Classical

theorem a_eq_sInf (S : Set ℕ) : (if S.Nonempty then sInf S else 0) = sInf S := by
  split_ifs with h
  · rfl
  · have h_empty : S = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      intro hx
      exact h ⟨x, hx⟩
    rw [h_empty]
    exact?
