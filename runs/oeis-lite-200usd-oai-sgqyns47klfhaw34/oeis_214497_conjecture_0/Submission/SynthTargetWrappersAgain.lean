import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#synth Subsingleton Target
#synth Decidable Target
#synth Nonempty Target
#synth Inhabited Target
#synth Unique Target
#synth IsEmpty Target

example : Target := by
  exact Classical.ofNonempty
