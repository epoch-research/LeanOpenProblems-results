import FormalConjectures.Util.ProblemImports
#check Finset.card_le_card_iff_of_subset
#check Finset.card_lt_card_iff_of_subset
#print axioms Finset.card_le_card_iff_of_subset
#print axioms Finset.card_lt_card_iff_of_subset
example : False := by
  have h := Finset.card_le_card_iff_of_subset (s := ({0}:Finset ℕ)) (t := ({0,1}:Finset ℕ)) (by simp)
  norm_num at h
  -- h : 2 ≤ 1 ↔ False, true
  exact h.mp (by norm_num)
