import FormalConjectures.Util.ProblemImports
open Set Classical

theorem sInf_eq_zero_of_not_mem (S : Set ℕ) (h1 : sInf S = 0) (h2 : 0 ∉ S) : S = ∅ := by
  by_contra h3
  have h4 : S.Nonempty := nonempty_iff_ne_empty.mpr h3
  have h5 : sInf S ∈ S := Nat.sInf_mem h4
  rw [h1] at h5
  exact h2 h5
