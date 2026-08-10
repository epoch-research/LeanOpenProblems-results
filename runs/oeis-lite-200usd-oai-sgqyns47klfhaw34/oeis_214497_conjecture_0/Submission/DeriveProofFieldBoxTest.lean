import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

structure BoxTarget where
  out : Target
-- try deriving instance after declaration
deriving instance Nonempty for BoxTarget

example : Target := (Classical.choice (inferInstance : Nonempty BoxTarget)).out
#print axioms instNonemptyBoxTarget

structure BoxMixed where
  x : Unit
  out : Target

deriving instance Nonempty for BoxMixed
example : Target := (Classical.choice (inferInstance : Nonempty BoxMixed)).out
#print axioms instNonemptyBoxMixed

structure BoxPropOnly : Prop where
  out : Target

deriving instance Nonempty for BoxPropOnly
example : Target := (Classical.choice (inferInstance : Nonempty BoxPropOnly)).out
#print axioms instNonemptyBoxPropOnly
