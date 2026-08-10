import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Finset.card_le_card_iff_of_subset (s := ({0} : Finset ℕ)) (t := ({0,1} : Finset ℕ)) (by simp)
  have ht : #({0,1} : Finset ℕ) ≤ #({0} : Finset ℕ) := by norm_num
  exact by
    have heq := h.mp ht
    norm_num at heq

example : False := by
  have h := Finset.card_lt_card_iff_of_subset (s := ({0,1} : Finset ℕ)) (t := ({0,1} : Finset ℕ)) (by simp)
  have hlt : #({0,1} : Finset ℕ) < #({0,1} : Finset ℕ) := by
    exact h.mpr (by decide)
  norm_num at hlt
