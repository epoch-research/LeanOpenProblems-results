import Mathlib

lemma foo : ¬ (Set.Finite {n : ℕ | n = n}) := by
  have : {n : ℕ | n = n} = Set.univ := by ext; simp
  rw [this]
  exact Set.infinite_univ
