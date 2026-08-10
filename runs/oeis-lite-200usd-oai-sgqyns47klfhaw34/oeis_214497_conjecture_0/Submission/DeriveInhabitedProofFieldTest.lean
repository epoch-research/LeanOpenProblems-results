import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

structure IBox where
  out : Target
  deriving Inhabited

example : Target := (default : IBox).out
#print axioms IBox.instInhabited

structure IBoxMixed where
  x : Nat
  out : Target
  deriving Inhabited

example : Target := (default : IBoxMixed).out
#print axioms IBoxMixed.instInhabited
