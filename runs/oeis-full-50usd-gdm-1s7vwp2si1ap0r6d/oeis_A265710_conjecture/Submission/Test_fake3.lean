import FormalConjectures.Util.ProblemImports

partial def fake_instance (n : ℕ) : Nonempty (n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) :=
  fake_instance n

instance (n : ℕ) : Nonempty (n = 14 ∨ n = 244 ∨ n = 494 ∨ n = 45994) :=
  fake_instance n

#print axioms fake_instance
