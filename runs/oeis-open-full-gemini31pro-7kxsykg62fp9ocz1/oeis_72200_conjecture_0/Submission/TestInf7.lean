import FormalConjectures.Util.ProblemImports
open Set

theorem a_eq_sInf (S : Set ℕ) : (if S.Nonempty then sInf S else 0) = sInf S := by
  split_ifs with h
  · rfl
  · exact Eq.symm Nat.sInf_empty
