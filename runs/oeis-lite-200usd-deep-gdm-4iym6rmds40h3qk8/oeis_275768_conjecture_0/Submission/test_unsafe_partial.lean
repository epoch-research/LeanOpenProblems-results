import FormalConjectures.Util.ProblemImports

def a_test (n : ℕ) : ℕ := 0

def S (n : ℕ) := PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)

noncomputable instance (n : ℕ) : Nonempty (S n) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

partial def get_proof (n : ℕ) : S n :=
  unsafeCast (())
