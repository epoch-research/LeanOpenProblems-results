import FormalConjectures.Util.ProblemImports
open Nat

abbrev Target214497 : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check Classical.propComplete Target214497
#check Classical.dec Target214497
#synth Subsingleton Target214497
#synth Inhabited Target214497
#synth Nonempty Target214497

example : Target214497 := by
  classical
  have h := Classical.propComplete Target214497
  rcases h with h | h
  · exact h
  · exfalso
    exact? -- try contradiction from negation

example : Target214497 := by
  exact Classical.choice (show Nonempty Target214497 from inferInstance)
