import Mathlib

theorem lemma_with_sorry : 1 = 2 := sorry

theorem my_false_thm : 1 = 2 := lemma_with_sorry

#print axioms my_false_thm
