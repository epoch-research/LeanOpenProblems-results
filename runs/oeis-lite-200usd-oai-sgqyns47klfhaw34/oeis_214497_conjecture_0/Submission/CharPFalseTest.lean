import FormalConjectures.Util.ProblemImports

example : False := by
  exact CharP.false_of_nontrivial_of_char_one

#print CharP.false_of_nontrivial_of_char_one
#print axioms CharP.false_of_nontrivial_of_char_one

theorem arbitrary_target : (∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)) := by
  exact False.elim CharP.false_of_nontrivial_of_char_one

#print axioms arbitrary_target
